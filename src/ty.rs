use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub struct Ty {
    pub kind: Kind
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

    pub fn new_record(fields: HashMap<String, Box<Ty>>) -> Ty {
        Ty { kind: Record(fields) }
    }
}
