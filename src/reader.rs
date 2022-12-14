use std::fmt;
use std::fmt::Formatter;
use std::iter::Peekable;
use std::str::Chars;
use crate::memory::Memory;
use crate::value::{Value, vec_into_list};

type PChars<'a> = Peekable<Chars<'a>>;

type Result<T> = std::result::Result<T, ReadError>;

#[derive(Debug, Clone)]
pub struct ReadError(String);

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "read error: {}", self.0)
    }
}

/// The `source` must be a valid s-expression.
/// Return its parsed form. `mem` is used to intern the symbols.
pub fn read(source: &str, mem: &mut Memory) -> Result<Value> {
    let mut iter = source.chars().peekable();
    read1(&mut iter, mem).map(|v| v.unwrap_or(Value::Nil))
}

fn read1(iter: &mut PChars, mem: &mut Memory) -> Result<Option<Value>> {
    skip_whitespace(iter);
    let maybe_next = iter.peek().map(|c| c.clone());
    let maybe_result = maybe_next.and_then(|c| {
        Some(match c {
            c if c.is_digit(10) || c == '-' => read_int(iter, mem),
            '(' => read_list(iter, mem),
            ')' => Ok(None),
            '\'' => read_quoted(iter, mem),
            _ => Ok(read_symbol(iter, mem)),
        })
    });
    maybe_result.unwrap_or(Ok(None))
}

fn skip_whitespace(iter: &mut PChars) {
    while iter.peek().map(|c| c.is_whitespace()).unwrap_or(false) {
        iter.next();
    }
}

fn must_see(expected: char, iter: &mut PChars, msg: &str) -> Result<()> {
    skip_whitespace(iter);
    if iter.next().map(|c| c == expected).unwrap_or(false) {
        Ok(())
    } else {
        Err(ReadError(String::from(msg)))
    }
}

fn read_list(iter: &mut PChars, mem: &mut Memory) -> Result<Option<Value>> {
    must_see('(', iter, "internal error: '(' expected")?;
    let mut contents = Vec::new();
    loop {
        match read1(iter, mem)? {
            None => break,
            Some(elem) => contents.push(elem),
        }
    }
    must_see(')', iter, "unterminated list")?;
    Ok(Some(vec_into_list(contents, mem)))
}

fn read_quoted(iter: &mut PChars, mem: &mut Memory) -> Result<Option<Value>> {
    must_see('\'', iter, "internal error: a quote char expected")?;
    let quoted = read1(iter, mem)?.unwrap();
    Ok(Some(vec_into_list(vec![mem.intern("quote"), quoted], mem)))
}

fn read_int(iter: &mut PChars, mem: &mut Memory) -> Result<Option<Value>> {
    let mut value = 0 as i64;
    let negative = if iter.peek() == Some(&'-') {
        // a minus may be a start of a negative number or just a minus symbol
        iter.next();
        match iter.peek() {
            None => return Ok(Some(mem.intern("-"))),
            Some(c) if !c.is_digit(10) => return Ok(Some(mem.intern("-"))),
            _ => {}
        }
        true
    } else {
        false
    };
    loop {
        match iter.peek() {
            None => break,
            Some(c) if c.is_whitespace() => break,
            Some('(') => break,
            Some(')') => break,
            Some('\'') => break,
            Some(c) => {
                match c.to_digit(10) {
                    None => return Err(ReadError(format!("invalid char in int literal: {:?}", c))),
                    Some(n) => value = value * 10 + (n as i64),
                }
            }
        }
        iter.next();
    }
    let final_value = if negative { -value } else { value };
    Ok(Some(Value::Int(final_value)))
}

fn read_symbol(iter: &mut PChars, mem: &mut Memory) -> Option<Value> {
    let mut chars = Vec::new();
    loop {
        match iter.peek() {
            None => break,
            Some('(') => break,
            Some(')') => break,
            Some('\'') => break,
            Some(c) if c.is_whitespace() => break,
            Some(c) => chars.push(c.clone()),
        }
        iter.next();
    }
    let str: String = chars.into_iter().collect();
    Some(mem.intern(&str))
}

#[cfg(test)]
pub mod test {
    use crate::memory::Memory;
    use crate::reader::read;
    use crate::value::{list_to_vec, Value};

    #[test]
    fn test_read_atoms() {
        let mut mem = Memory::new();
        assert_eq!(read("foo", &mut mem).unwrap(), mem.intern("foo"));
        assert_eq!(read("foo-bar", &mut mem).unwrap(), mem.intern("foo-bar"));
        assert_eq!(read("42", &mut mem).unwrap(), Value::Int(42));
        assert_eq!(read("-1234", &mut mem).unwrap(), Value::Int(-1234));
        assert_eq!(read("-", &mut mem).unwrap(), mem.intern("-"));
    }

    #[test]
    fn test_read_list() {
        let mut mem = Memory::new();
        let foo = mem.intern("foo");
        let bar = mem.intern("bar");
        let list1 = read("(foo bar)", &mut mem).unwrap();
        assert_eq!(list_to_vec(&list1), vec![foo.clone(), bar.clone()]);
        let list2 = read("(foo)", &mut mem).unwrap();
        assert_eq!(list_to_vec(&list2), vec![foo.clone()]);
        let list3 = read("()", &mut mem).unwrap();
        assert_eq!(list_to_vec(&list3), vec![]);
    }

    #[test]
    fn test_read_nested_lists() {
        let mut mem = Memory::new();
        let foo = mem.intern("foo");
        let bar = mem.intern("bar");
        let list = read("(foo (bar foo))", &mut mem).unwrap();
        let v = list_to_vec(&list);
        assert_eq!(v.len(), 2);
        assert_eq!(v[0], foo);
        assert_eq!(list_to_vec(&v[1]), vec![bar, foo]);
    }

    #[test]
    fn test_read_nested_lists_2() {
        let mut mem = Memory::new();
        let foo = mem.intern("foo");
        let bar = mem.intern("bar");
        let list = read("(foo (bar bar) (foo foo))", &mut mem).unwrap();
        let v = list_to_vec(&list);
        assert_eq!(v.len(), 3);
        assert_eq!(v[0], foo);
        assert_eq!(list_to_vec(&v[1]), vec![bar.clone(), bar.clone()]);
        assert_eq!(list_to_vec(&v[2]), vec![foo.clone(), foo.clone()]);
    }

    #[test]
    fn test_read_quote()  {
        let mut mem = Memory::new();
        let foo = mem.intern("foo");
        let expr = read("'foo", &mut mem).unwrap();
        let vec = list_to_vec(&expr);
        assert_eq!(vec, vec![mem.intern("quote"), foo]);
    }
}
