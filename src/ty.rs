use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub struct Ty {
    pub kind: Kind
}

pub struct Fields {
    elements: HashMap<String, Box<Ty>>
}

impl Fields {
    pub fn new() -> Fields {
        Fields { elements: HashMap::new() }
    }

    pub fn insert(&mut self, k: String, v: Box<Ty>) -> Option<Box<Ty>> {
        self.elements.insert(k, v)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Arrow(Box<Ty>, Box<Ty>), // e.g. Bool -> Bool
    Bool,
    Nat, // Natural Number
    Record(HashMap<String, Box<Ty>>),
    Unit, // the only value of Unit type is "unit"
}

use self::Kind::*;

impl Ty {
    pub fn new_arrow(l: Ty, r: Ty) -> Ty {
        Ty { kind: Arrow(Box::new(l), Box::new(r)) }
    }

    pub fn new_bool() -> Ty {
        Ty { kind: Bool }
    }

    pub fn new_nat() -> Ty {
        Ty { kind: Nat }
    }

    pub fn new_unit() -> Ty {
        Ty { kind: Unit }
    }

    pub fn new_record(fields: Fields) -> Ty {
        Ty { kind: Record(fields.elements) }
    }
}
