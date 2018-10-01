#[derive(Debug, PartialEq)]
pub struct Value {
    kind: Kind
}

#[derive(Debug, PartialEq)]
pub enum Kind {
    None,
    True,
    False,
}

use self::Kind::*;

impl Value {
    pub fn new_none() -> Value {
        Value { kind: None }
    }

    pub fn new_true() -> Value {
        Value { kind: True }
    }

    pub fn new_false() -> Value {
        Value { kind: False }
    }
}
