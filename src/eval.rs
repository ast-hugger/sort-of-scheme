use std::fmt;
use std::fmt::Formatter;
use crate::builtins::{Fun, populate_root_environment};
use crate::memory::{Closure, Environment, Memory};
use crate::value::{list_to_vec, Value};

pub type Result<T> = std::result::Result<T, EvalError>;

#[derive(Clone, Debug)]
pub struct EvalError(pub String);

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "evaluation error: {}", self.0)
    }
}

pub struct Evaluator {
    pub memory: Memory,
    root: Environment,
    syms: UsefulSymbols,
}

struct UsefulSymbols {
    define: Value,
    if_sym: Value,
    lambda: Value,
    let_sym: Value,
    quote: Value,
    set_bang: Value,
}

macro_rules! error_if_not {
    ($expr: expr, $($arg: tt)*) => {
        if !$expr {
            return Err(EvalError(format!($($arg)*)))
        }
    }
}

impl Evaluator {
    pub fn new() -> Self {
        let mut memory = Memory::new();
        let root = memory.new_environment(None);
        populate_root_environment(&root, &mut memory);
        let syms = Self::new_useful_symbols(&mut memory);
        Evaluator { memory, root, syms }
    }

    fn new_useful_symbols(memory: &mut Memory) -> UsefulSymbols {
        UsefulSymbols {
            define: memory.intern("define"),
            if_sym: memory.intern("if"),
            lambda: memory.intern("lambda"),
            let_sym: memory.intern("let"),
            quote: memory.intern("quote"),
            set_bang: memory.intern("set!"),
        }
    }

    pub fn evaluate(&mut self, expr: &Value) -> Result<Value> {
        self.eval(expr, &self.root.clone())
    }

    fn eval(&mut self, expr: &Value, env: &Environment) -> Result<Value> {
        match expr {
            Value::Nil => Ok(expr.clone()),
            Value::Bool(_) => Ok(expr.clone()),
            Value::Int(_) => Ok(expr.clone()),
            Value::String(_) => Ok(expr.clone()),
            Value::Symbol(_) =>
                env.lookup(expr)
                    .map(|v| v.clone())
                    .ok_or(EvalError(format!("undefined variable: {}", expr))),
            Value::Pair(_) => self.eval_form(expr, env),
            _ => Err(EvalError(format!("unrecognized expression: {}", expr))),
        }
    }

    fn eval_form(&mut self, form: &Value, env: &Environment) -> Result<Value> {
        match form.car() {
            it @ Value::Symbol(_) if *it == self.syms.if_sym => {
                let rest = form.cdr();
                error_if_not!(rest.is_pair(), "invalid if form: {}", form);
                let cond = rest.car();
                let rest2 = rest.cdr();
                error_if_not!(rest2.is_pair(), "invalid if form: {}", form);
                let true_branch = rest2.car();
                let false_branch = match rest2.cdr() {
                    it @ Value::Pair(_) => Some(it.car()),
                    Value::Nil => None,
                    _ => return Err(EvalError(format!("invalid if form: {}", form))),
                };
                match self.eval(&cond, env)? {
                    Value::Bool(true) => {
                        self.eval(&true_branch, env)
                    }
                    Value::Bool(false) => {
                        false_branch.map(|it| self.eval(it, env)).unwrap_or(Ok(Value::Nil))
                    }
                    other => return Err(EvalError(format!("condition value not a boolean: {}", other)))
                }
            }
            it @ Value::Symbol(_) if *it == self.syms.let_sym => {
                let rest = form.cdr();
                let mut bindings = rest.car();
                error_if_not!(bindings.is_pair(), "invalid let bindings: {}", bindings);
                let new_env = self.memory.new_environment(Some(env.clone()));
                while !bindings.is_nil() {
                    let binding = bindings.car();
                    let var = binding.car();
                    let expr = binding.cdr().car();
                    error_if_not!(var.is_symbol(), "invalid let binding var: {}", var);
                    let value = self.eval(expr, env)?;
                    new_env.bind(var, value);
                    bindings = bindings.cdr();
                }
                let mut exprs = rest.cdr();
                let mut last = Value::Nil;
                while !exprs.is_nil() {
                    let expr = exprs.car();
                    last = self.eval(expr, &new_env)?;
                    exprs = exprs.cdr();
                }
                Ok(last)
            },
            it @ Value::Symbol(_) if *it == self.syms.quote => {
                let tail = form.cdr();
                error_if_not!(tail.cdr().is_nil(), "extraneous forms in: {}", form);
                Ok(tail.car().clone())
            },
            it @ Value::Symbol(_) if *it == self.syms.lambda => {
                let rest = form.cdr();
                let args = rest.car();
                error_if_not!(args.is_pair(), "invalid lambda args: {}", args);
                let body = rest.cdr();
                error_if_not!(body.is_pair(), "invalid lambda body: {}", body);
                let closure = Closure {
                    environment: env.clone(),
                    args: list_to_vec(args),
                    exprs: list_to_vec(body),
                };
                Ok(self.memory.new_function(closure))
            },
            it @ Value::Symbol(_) if *it == self.syms.set_bang => {
                let rest = form.cdr();
                let var = rest.car();
                error_if_not!(var.is_symbol(), "invalid set! var: {}", var);
                let expr = rest.cdr().car();
                error_if_not!(rest.cdr().cdr().is_nil(), "extraneous forms in: {}", form);
                let value = self.eval(expr, env)?;
                env.set(var, value);
                Ok(Value::Nil)
            },
            it @ Value::Symbol(_) if *it == self.syms.define => {
                let rest = form.cdr();
                error_if_not!(rest.is_pair(), "invalid define form: {}", form);
                let rest2 = rest.cdr(); // elems past the first two (i.e. past define and one more)
                error_if_not!(rest2.is_pair(), "invalid define form: {}", form);
                let (var, value) = match rest.car() {
                    // (define var expr)
                    var @ Value::Symbol(_) => {
                        error_if_not!(rest2.cdr().is_nil(), "invalid define form: {}", form);
                        let expr = rest2.car();
                        let value = self.eval(&expr, env)?; // show we eval in env or root?
                        (var, value)
                    }
                    // (define (fun-name arg*) expr+)
                    list @ Value::Pair(_) => {
                        let name = list.car();
                        error_if_not!(name.is_symbol(), "invalid name in: {}", form);
                        let args = list.cdr();
                        error_if_not!(args.is_pair() || args.is_nil(), "invalid args in: {}", form);
                        let args_and_body = self.memory.cons(args.clone(), rest2.clone());
                        let lambda_expr = self.memory.cons(self.syms.lambda.clone(), args_and_body);
                        let lambda = self.eval(&lambda_expr, env)?;
                        (name, lambda)
                    }
                    // anything not the above
                    _ => {
                        return Err(EvalError(format!("invalid define form: {}", form)))
                    }
                };
                self.root.bind(&var, value);
                Ok(var.clone())
            }
            it => {
                let car_value = self.eval(it, env)?;
                let mut args = Vec::new();
                let mut head = form.cdr();
                error_if_not!(head.is_pair() || form.is_nil(), "bad call form: {}", form);
                while !head.is_nil() {
                    let expr = head.car();
                    let val = self.eval(expr, env)?;
                    args.push(val);
                    head = head.cdr();
                }
                self.apply(&car_value, &args)
            }
        }
    }

    fn apply(&mut self, fun: &Value, args: &Vec<Value>) -> Result<Value> {
        match fun {
            Value::Builtin(builtin) => match builtin.fun {
                Fun::F0(f) => {
                    error_if_not!(args.len() == 0, "{} expects 0 args, got: {}", builtin.name, args.len());
                    f()
                },
                Fun::F1(f) => {
                    error_if_not!(args.len() == 1, "{} expects 1 arg, got: {}", builtin.name, args.len());
                    f(&args[0])
                },
                Fun::F2(f) => {
                    error_if_not!(args.len() == 2, "{} expects 2 args, got: {}", builtin.name, args.len());
                    f(&args[0], &args[1])
                },
            }
            Value::Function(closure) => {
                let (closure_env, params, exprs) = unsafe {
                    let c = &**closure;
                    (&c.environment, &c.args, &c.exprs)
                };
                let eval_env = self.memory.new_environment(Some(closure_env.clone()));
                error_if_not!(params.len() == args.len(),
                    "closure expects {} args, called with {}", params.len(), args.len());
                for i in 0..params.len() {
                    eval_env.bind(&params[i], args[i].clone());
                }
                let mut result = Value::Nil;
                for expr in exprs {
                    result = self.eval(expr, &eval_env)?;
                }
                Ok(result)
            }
            _ => Err(EvalError(format!("unexpected function: {:?}", fun)))
        }
    }
}

#[cfg(test)]
pub mod test {
    use crate::eval::Evaluator;
    use crate::reader;
    use crate::value::Value;

    #[test]
    fn self_evaluating() {
        let mut lisp = Evaluator::new();
        let mut v = lisp.evaluate(&Value::Nil).unwrap();
        assert_eq!(v, Value::Nil);
        v = lisp.evaluate(&Value::string("hi")).unwrap();
        assert_eq!(v, Value::string("hi"));
        v = lisp.evaluate(&Value::Int(42)).unwrap();
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn eval_symbol() {
        let mut lisp = Evaluator::new();
        let sym = lisp.memory.intern("foo");
        lisp.root.bind(&sym, Value::Int(42));
        let result = lisp.evaluate(&sym).unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn eval_quote() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("'foo", &mut lisp.memory).unwrap();
        let result = lisp.evaluate(&expr).unwrap();
        assert_eq!(result, lisp.memory.intern("foo"))
    }

    #[test]
    fn call_builtin() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("(car '(foo bar))", &mut lisp.memory).unwrap();
        let result = lisp.evaluate(&expr).unwrap();
        assert_eq!(result, lisp.memory.intern("foo"));
        let expr2 = reader::read("(car (cdr '(foo bar)))", &mut lisp.memory).unwrap();
        let result2 = lisp.evaluate(&expr2).unwrap();
        assert_eq!(result2, lisp.memory.intern("bar"))
    }

    #[test]
    fn eval_closure() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("(lambda (c) (car c) (cdr c))", &mut lisp.memory).unwrap();
        if let Value::Function(closure) = lisp.evaluate(&expr).unwrap() {
            unsafe {
                let args = &(*closure).args;
                assert_eq!(args.len(), 1);
                let exprs = &(*closure).exprs;
                assert_eq!(exprs.len(), 2);
            }
        } else {
            panic!()
        }
    }

    #[test]
    fn apply_closure() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("((lambda (x y) (+ x y)) 3 4)", &mut lisp.memory).unwrap();
        let result = lisp.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(7));
    }

    #[test]
    fn eval_let() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("(let ((x 3) (y 4)) (+ x y))", &mut lisp.memory).unwrap();
        let result = lisp.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(7));
    }

    #[test]
    fn eval_set() {
        let mut lisp = Evaluator::new();
        lisp.root.bind(&lisp.memory.intern("foo"), Value::Int(0));
        let expr = reader::read("(let ((x 3)) (set! foo 4) (+ x foo))", &mut lisp.memory).unwrap();
        let result = lisp.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(7));
    }

    #[test]
    fn define_var() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("(define foo (+ 3 4))", &mut lisp.memory).unwrap();
        let _ = lisp.evaluate(&expr).unwrap();
        let expr2 = reader::read("foo", &mut lisp.memory).unwrap();
        let result = lisp.evaluate(&expr2).unwrap();
        assert_eq!(result, Value::Int(7));
    }

    #[test]
    fn define_fun() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("(define (inc n) (+ n 1))", &mut lisp.memory).unwrap();
        let _ = lisp.evaluate(&expr).unwrap();
        let expr2 = reader::read("(inc 3)", &mut lisp.memory).unwrap();
        let result = lisp.evaluate(&expr2).unwrap();
        assert_eq!(result, Value::Int(4));
    }

    #[test]
    fn test_if() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("(define (comp a b) (if (= a b) 'equal 'not-equal))", &mut lisp.memory).unwrap();
        let _ = lisp.evaluate(&expr).unwrap();
        {
            let expr2 = reader::read("(comp 3 3)", &mut lisp.memory).unwrap();
            let result = lisp.evaluate(&expr2).unwrap();
            assert_eq!(result, lisp.memory.intern("equal"));
        }
        {
            let expr2 = reader::read("(comp 3 4)", &mut lisp.memory).unwrap();
            let result = lisp.evaluate(&expr2).unwrap();
            assert_eq!(result, lisp.memory.intern("not-equal"));
        }
    }

    #[test]
    fn test_if_2() {
        let mut lisp = Evaluator::new();
        let expr = reader::read("(define (comp a b) (if (= a b) 'equal))", &mut lisp.memory).unwrap();
        let _ = lisp.evaluate(&expr).unwrap();
        {
            let expr2 = reader::read("(comp 3 3)", &mut lisp.memory).unwrap();
            let result = lisp.evaluate(&expr2).unwrap();
            assert_eq!(result, lisp.memory.intern("equal"));
        }
        {
            let expr2 = reader::read("(comp 3 4)", &mut lisp.memory).unwrap();
            let result = lisp.evaluate(&expr2).unwrap();
            assert_eq!(result, Value::Nil);
        }
    }
}
