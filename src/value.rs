use node::{Node};
use ty::{Ty};

#[derive(Clone, Debug, PartialEq)]
pub struct Value {
    pub kind: Kind
}

#[derive(Clone, Debug, PartialEq)]
pub struct Fields {
    elements: Vec<(String, Box<Value>)>
}

impl Fields {
    pub fn new() -> Fields {
        Fields { elements: Vec::new() }
    }

    pub fn insert(&mut self, k: String, v: Box<Value>) {
        self.elements.push((k, v))
    }

//     pub fn iter(&self) -> ::std::slice::Iter<(String, Box<Node>)> {
//         self.elements.iter()
//     }

    pub fn get(&self, k: &str) -> Option<&Box<Value>>
    {
        for (i, (s, n)) in self.elements.iter().enumerate() {
            if s == k { return Some(n) }
            if i.to_string() == k { return Some(n) }
        }

        ::std::option::Option::None
    }
}


#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    None,
    True,
    False,
    Unit,
    Nat(u32),
    Lambda(Node),
    Record(Fields),
    Tag(String, Box<Value>, Box<Ty>),
    TyAbs(String, String, Box<Node>) // Type abstruction is value (P. 270)
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

    pub fn new_unit() -> Value {
        Value { kind: Unit }
    }

    pub fn new_nat(i: u32) -> Value {
        Value { kind: Nat(i) }
    }

    pub fn new_lambda(node: Node) -> Value {
        Value { kind: Lambda(node) }
    }

    pub fn new_record(fields: Fields) -> Value {
        Value { kind: Record(fields) }
    }

    pub fn new_tag(s: String, value: Value, ty: Ty) -> Value {
        Value { kind: Tag(s, Box::new(value), Box::new(ty)) }
    }

    pub fn new_ty_abs(gen_name: String, orig_name: String, node: Node) -> Value {
        Value { kind: TyAbs(gen_name, orig_name, Box::new(node)) }
    }
}
