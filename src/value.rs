use node::{Node};

#[derive(Clone, Debug, PartialEq)]
pub struct Value {
    pub kind: Kind
}

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    None,
    True,
    False,
    Nat(u32),
    Lambda(Node),
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

    pub fn new_nat(i: u32) -> Value {
        Value { kind: Nat(i) }
    }

    pub fn new_lambda(node: Node) -> Value {
        Value { kind: Lambda(node) }
    }
}
