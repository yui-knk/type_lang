#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct Ty {
    pub kind: Kind
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Kind {
    Arrow(Box<Ty>, Box<Ty>), // e.g. Bool -> Bool
    Bool,
    Nat, // Natural Number
    Id(String), // Type variable
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

    pub fn new_id(str: String) -> Ty {
        Ty { kind: Id(str) }
    }
}
