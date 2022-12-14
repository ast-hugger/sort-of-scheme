use std::clone::Clone;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use crate::eval;
use crate::memory::{Environment, Memory};
use crate::value::Value;

pub struct Builtin {
    pub name: &'static str,
    pub fun: Fun
}

impl Debug for Builtin {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl PartialEq for Builtin {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }

    fn ne(&self, other: &Self) -> bool {
        self.name != other.name
    }
}

impl Eq for Builtin {

}

impl Hash for Builtin {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

pub enum Fun {
    F0(fn () -> eval::Result<Value>),
    F1(fn (&Value) -> eval::Result<Value>),
    F2(fn (&Value, &Value) -> eval::Result<Value>),
}

macro_rules! error_if_not {
    ($expr: expr, $($arg: tt)*) => {
        if !$expr {
            return Err(eval::EvalError(format!($($arg)*)))
        }
    }
}

/*
        The builtins
 */

pub fn populate_root_environment(root: &Environment, memory: &mut Memory) {
    macro_rules! define_builtin {
        ($b: expr) => { root.bind(&memory.intern($b.name), Value::Builtin(&$b)) }
    }
    define_builtin!(CAR);
    define_builtin!(CDR);

    define_builtin!(PLUS);
    define_builtin!(MINUS);
    define_builtin!(MULTIPLY);
    define_builtin!(DIVIDE);

    define_builtin!(EQ);
    define_builtin!(LT);
    define_builtin!(LTE);
    define_builtin!(GT);
    define_builtin!(GTE);
}

const CAR: Builtin = Builtin {
    name: "car",
    fun: Fun::F1(|arg: &Value| {
        error_if_not!(arg.is_pair(), "car arg is not a pair: {}", arg);
        Ok(arg.car().clone())
    })
};

const CDR: Builtin = Builtin {
    name: "cdr",
    fun: Fun::F1(|arg: &Value| {
        error_if_not!(arg.is_pair(), "cdr arg is not a pair: {}", arg);
        Ok(arg.cdr().clone())
    })
};

macro_rules! binary_int_op {
    ($name: expr, $a: ident, $b: ident, $expr: expr) => {
        Builtin {
            name: $name,
            fun: Fun::F2(|x: &Value, y: &Value| {
                match x {
                    Value::Int($a) => match y {
                        Value::Int($b) => Ok(Value::Int($expr)),
                        other => Err(eval::EvalError(format!("the arg of {} is not an int: {}", $name, other)))
                    },
                    other => Err(eval::EvalError(format!("the arg of {} is not an int: {}", $name, other)))
                }
            })
        }
    }
}

const PLUS: Builtin = binary_int_op!("+", a, b, a + b);
const MINUS: Builtin = binary_int_op!("-", a, b, a - b);
const MULTIPLY: Builtin = binary_int_op!("*", a, b, a * b);
const DIVIDE: Builtin = binary_int_op!("/", a, b, a / b);

macro_rules! binary_int_predicate {
    ($name: expr, $a: ident, $b: ident, $expr: expr) => {
        Builtin {
            name: $name,
            fun: Fun::F2(|x: &Value, y: &Value| {
                match x {
                    Value::Int($a) => match y {
                        Value::Int($b) => Ok(Value::Bool($expr)),
                        other => Err(eval::EvalError(format!("the arg of {} is not an int: {}", $name, other)))
                    },
                    other => Err(eval::EvalError(format!("the arg of {} is not an int: {}", $name, other)))
                }
            })
        }
    }
}

const EQ: Builtin = binary_int_predicate!("=", a, b, a == b);
const LT: Builtin = binary_int_predicate!("<", a, b, a < b);
const LTE: Builtin = binary_int_predicate!("<=", a, b, a <= b);
const GT: Builtin = binary_int_predicate!(">", a, b, a > b);
const GTE: Builtin = binary_int_predicate!(">=", a, b, a >= b);
