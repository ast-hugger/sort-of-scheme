use std::fmt::{Debug, Display, Formatter};
use crate::builtins::Builtin;
use crate::memory::{Closure, ConsCell, Memory};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    String(String),
    Symbol(*const String),
    Pair(*mut ConsCell),
    Builtin(&'static Builtin),
    Function(*const Closure),
}

macro_rules! value_type_predicate {
    ($name: ident, $variant: pat) => {
        pub fn $name(&self) -> bool {
            match self {
                $variant => true,
                _ => false,
            }
        }
    }
}

impl Value {
    pub fn string(contents: &str) -> Value {
        Value::String(String::from(contents))
    }

    value_type_predicate!(is_nil, Value::Nil);
    value_type_predicate!(is_bool, Value::Bool(_));
    value_type_predicate!(is_int, Value::Int(_));
    value_type_predicate!(is_string, Value::String(_));
    value_type_predicate!(is_symbol, Value::Symbol(_));
    value_type_predicate!(is_pair, Value::Pair(_));
    value_type_predicate!(is_builtin, Value::Builtin(_));
    value_type_predicate!(is_function, Value::Function(_));

    pub fn car(&self) -> &Value {
        match self {
            Value::Pair(cons) => unsafe { &(*(*cons)).car },
            _ => panic!(),
        }
    }

    pub fn cdr(&self) -> &Value {
        match self {
            Value::Pair(cons) => unsafe { &(*(*cons)).cdr },
            _ => panic!(),
        }
    }

    pub fn set_car(&self, v: Value) {
        match self {
            Value::Pair(cons) => unsafe { (*(*cons)).car = v },
            _ => panic!(),
        }
    }

    pub fn set_cdr(&self, v: Value) {
        match self {
            Value::Pair(cons) => unsafe { (*(*cons)).cdr = v },
            _ => panic!(),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(v) => write!(f, "{}", v),
            Value::Int(v) => write!(f, "{}", v),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Symbol(s) => {
                let str = unsafe { &**s };
                write!(f, "{}", str)
            }
            Value::Pair(_) => {
                write!(f, "(").expect("the unexpected");
                let mut head = self;
                let mut is_first = true;
                while !head.is_nil() {
                    if !is_first {
                        write!(f, " ").expect("the unexpected");
                    } else {
                        is_first = false;
                    }
                    write!(f, "{}", head.car()).expect("the unexpected");
                    head = head.cdr();
                    if !(head.is_pair() || head.is_nil()) {
                        write!(f, " . {}", head).expect("the unexpected");
                        break;
                    }
                }
                write!(f, ")")
            }
            Value::Builtin(b) => write!(f, "<builtin: {}>", b.name),
            Value::Function(_) => write!(f, "<closure>"),
        }
    }
}

pub fn list_to_vec(list: &Value) -> Vec<Value> {
    let mut result = Vec::new();
    let mut here = list;
    while !here.is_nil() {
        result.push(here.car().clone());
        here = here.cdr();
    }
    result
}

/// Create a chain of cons cells allocated using the given memory
/// with the contents of the given vector. The values held by the
/// vector are moved into the list.
pub fn vec_into_list(vec: Vec<Value>, mem: &mut Memory) -> Value {
    let mut tail = Value::Nil;
    for v in vec.into_iter().rev() {
        tail = mem.cons(v, tail)
    }
    tail
}

#[cfg(test)]
pub mod test {
    use crate::memory::Memory;
    use crate::reader;
    use crate::value::{list_to_vec, Value, vec_into_list};

    #[test]
    fn predicates() {
        let mut mem = Memory::new();
        assert!(Value::Nil.is_nil());
        assert!(!Value::Int(42).is_nil());
        assert!(mem.intern("foo").is_symbol());
        assert!(!Value::Int(42).is_symbol());
        let pair = mem.cons(Value::Int(3), Value::Int(4));
        assert!(pair.is_pair());
        assert!(!Value::Int(42).is_pair());
    }

    #[test]
    fn car_and_cdr() {
        let mut mem = Memory::new();
        let pair = mem.cons(Value::Int(3), Value::Int(4));
        assert_eq!(pair.car(), &Value::Int(3));
        assert_eq!(pair.cdr(), &Value::Int(4));
        pair.set_car(Value::string("hi"));
        pair.set_cdr(Value::string("bye"));
        assert_eq!(pair.car(), &Value::string("hi"));
        assert_eq!(pair.cdr(), &Value::string("bye"));
    }

    #[test]
    fn test_list_to_vec() {
        let mut mem = Memory::new();
        let cell3 = mem.cons(Value::Int(3), Value::Nil);
        let cell2 = mem.cons(Value::Int(2), cell3);
        let cell1 = mem.cons(Value::Int(1), cell2);
        let vec = list_to_vec(&cell1);
        assert_eq!(vec.len(), 3);
        assert_eq!(vec[0], Value::Int(1));
        assert_eq!(vec[1], Value::Int(2));
        assert_eq!(vec[2], Value::Int(3));
    }

    #[test]
    fn test_vec_into_list() {
        let mut mem = Memory::new();
        let list = vec_into_list(vec![Value::Int(1), Value::Int(2)], &mut mem);
        let vec = list_to_vec(&list);
        assert_eq!(vec.len(), 2);
        assert_eq!(vec[0], Value::Int(1));
        assert_eq!(vec[1], Value::Int(2));
    }

    #[test]
    fn value_display() {
        let mut mem = Memory::new();
        assert_eq!(format!("{}", Value::Nil), "nil");
        assert_eq!(format!("{}", Value::Int(42)), "42");
        assert_eq!(format!("{}", Value::string("hi")), "\"hi\"");
        assert_eq!(format!("{}", mem.intern("foo")), "foo");
        read_and_display("()", "nil", &mut mem);
        read_and_display("(foo)", "(foo)", &mut mem);
        read_and_display("(foo 42 bar)", "(foo 42 bar)", &mut mem);
        read_and_display("(foo (4 2) bar)", "(foo (4 2) bar)", &mut mem);
        let cell = mem.cons(Value::Int(3), Value::Int(4));
        assert_eq!(format!("{}", cell), "(3 . 4)")
    }

    fn read_and_display(source: &str, expected: &str, mem: &mut Memory) {
        let list = reader::read(source, mem).unwrap();
        assert_eq!(format!("{}", list), expected);
    }
}