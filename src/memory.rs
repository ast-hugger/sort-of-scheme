use std::alloc::{alloc, Layout};
use std::collections::HashMap;
use std::{alloc, ptr};

use crate::value::{Value};
use crate::value::Value::Pair;

pub struct Memory {
    cells: Page<ConsCell>,
    symbols: Page<String>,
    symbol_table: HashMap<String, *const String>,
    envs: Page<Env>,
    closures: Page<Closure>,
}

impl Memory {
    pub fn new() -> Memory {
        Memory {
            cells: Page::new(1000),
            symbols: Page::new(1000),
            symbol_table: HashMap::new(),
            envs: Page::new(100),
            closures: Page::new(100)
        }
    }

    pub fn cons(&mut self, car: Value, cdr: Value) -> Value {
        let cell = ConsCell { car, cdr };
        let ptr = self.cells.insert(cell).unwrap();
        Pair(ptr)
    }

    pub fn intern(&mut self, string: &str) -> Value {
        match self.symbol_table.get(string) {
            Some(ptr) => Value::Symbol(*ptr),
            None => {
                let s = String::from(string);
                let ptr = self.symbols.insert(s.clone()).unwrap();
                self.symbol_table.insert(s, ptr);
                Value::Symbol(ptr)
            }
        }
    }

    pub fn new_environment(&mut self, parent: Option<Environment>) -> Environment {
        let e = Env {
            parent,
            bindings: HashMap::new()
        };
        Environment(self.envs.insert(e).unwrap())
    }

    pub fn new_function(&mut self, closure: Closure) -> Value {
        let ptr = self.closures.insert(closure).unwrap();
        Value::Function(ptr)
    }
}

struct Page<T> {
    capacity: usize,
    data: *mut T,
    map: Vec<bool>,
    next_try: usize
}

impl<T> Page<T> {
    pub fn new(capacity: usize) -> Self {
        let layout = Layout::array::<T>(capacity).unwrap();
        let data = unsafe {
            alloc(layout) as *mut T
        };
        Page {
            capacity,
            data,
            map: vec![false; capacity],
            next_try: 0
        }
    }

    // Find an empty slot for the value, move the value into it,
    // and return Ok with a mutable pointer to the slot.
    // If there are no vacant slots, give the value back inside an Err.
    pub fn insert(&mut self, value: T) -> Result<*mut T, T> {
        match self.find_free_index() {
            Some(i) => unsafe {
                self.next_try = i + 1;
                let slot = self.data.offset(i as isize);
                ptr::write(slot, value);
                Ok(slot)
            }
            None => Err(value)
        }
    }

    fn find_free_index(&self) -> Option<usize> {
        let mut i = self.next_try;
        for _ in 0..self.capacity {
            if !self.map[i] { return Some(i) }
            i = (i + 1) % self.capacity
        }
        None
    }

    // Move the value in the pointed-to slot out of the page.
    // The slot becomes vacant. The pointer must point within the page.
    #[allow(dead_code)] // not using it for now, but planning to in the future
    pub fn extract(&mut self, slot: *mut T) -> T {
        unsafe {
            let index = slot.offset_from(self.data);
            assert!(index > 0 && index < self.capacity as isize);
            let i = index as usize;
            assert!(self.map[i]);
            self.map[i] = false;
            ptr::read(slot)
        }
    }
}

impl<T> Drop for Page<T> {
    fn drop(&mut self) {
        for i in 0..self.capacity {
            if self.map[i] {
                unsafe {
                    let slot = self.data.offset(i as isize);
                    ptr::read(slot); // move the value out of the slot to let it drop
                }
            }
        }
        // And now deallocate the data area
        let layout = Layout::array::<T>(self.capacity).unwrap();
        unsafe { alloc::dealloc(self.data as *mut u8, layout) }
    }
}

#[derive(Debug)]
pub struct ConsCell {
    pub car: Value,
    pub cdr: Value,
}

#[derive(Copy, Clone, Debug)]
pub struct Environment(*mut Env);

#[derive(Debug)]
struct Env {
    parent: Option<Environment>,
    bindings: HashMap<Value, Value>,
}

impl Environment {
    pub fn lookup(&self, key: &Value) -> Option<&Value> {
        assert!(key.is_symbol());
        let env = unsafe { &*self.0 };
        let local = env.bindings.get(key);
        local.or_else(|| env.parent.as_ref().and_then(|it| it.lookup(key)))
    }

    /// Bind the key, which must be a symbol, to the given value in this environment.
    /// See also `set()`.
    pub fn bind(&self, key: &Value, value: Value) {
        assert!(key.is_symbol());
        let env = unsafe { &mut *self.0 };
        env.bindings.insert(key.clone(), value);
    }

    /// The key must already be bound in this environment or one of its parents.
    /// Change the binding in that environment to the given value.
    pub fn set(&self, key: &Value, value: Value) {
        let env = unsafe { &*self.0 };
        if env.bindings.contains_key(key) {
            self.bind(key, value);
        } else if env.parent.is_some() {
            env.parent.unwrap().set(key, value);
        } else {
            panic!("undefined variable: {:?}", key);
        }
    }
}

#[derive(Debug)]
pub struct Closure {
    pub environment: Environment,
    pub args: Vec<Value>,
    pub exprs: Vec<Value>,
}

#[cfg(test)]
pub mod test {
    use crate::memory::Memory;
    use crate::value::Value;
    use super::Page;

    #[test]
    fn pages() {
        let mut table: Page<String> = Page::new(10);
        let v = table.insert(String::from("nothing")).unwrap();
        unsafe {
            *v = String::from("hello");
        }
        let _v2 = table.insert(String::from("bye")).unwrap();
        unsafe {
            assert_eq!(*v, "hello");
        }
    }

    #[test]
    fn symbols() {
        let mut mem = Memory::new();
        let foo1 = mem.intern("foo");
        let foo2 = mem.intern("foo");
        let bar = mem.intern("bar");
        assert_eq!(foo1, foo2);
        assert_ne!(foo1, bar);
    }

    #[test]
    fn environments() {
        let mut mem = Memory::new();
        let parent = mem.new_environment(None);
        let child = mem.new_environment(Some(parent));
        let foo = mem.intern("foo");
        let bar = mem.intern("bar");
        let bogus = mem.intern("bogus");
        parent.bind(&foo, Value::Int(3));
        parent.bind(&bar, Value::Int(42));
        child.bind(&foo, Value::Int(4));
        // TODO is there an idiomatic API for the map below?
        assert_eq!(parent.lookup(&foo).map(|it| it.clone()), Some(Value::Int(3)));
        assert_eq!(parent.lookup(&bar).map(|it| it.clone()), Some(Value::Int(42)));
        assert_eq!(child.lookup(&foo).map(|it| it.clone()), Some(Value::Int(4)));
        assert_eq!(child.lookup(&bar).map(|it| it.clone()), Some(Value::Int(42)));
        assert_eq!(child.lookup(&bogus), None);
    }
}
