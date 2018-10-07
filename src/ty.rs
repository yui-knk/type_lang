#[derive(Clone, Debug, PartialEq)]
pub struct Ty {
    pub kind: Kind
}

#[derive(Clone, Debug, PartialEq)]
pub struct Fields {
    elements: Vec<(String, Box<Ty>)>
}

impl Fields {
    pub fn new() -> Fields {
        Fields { elements: Vec::new() }
    }

    pub fn insert(&mut self, k: String, v: Box<Ty>) {
        self.elements.push((k, v))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Arrow(Box<Ty>, Box<Ty>), // e.g. Bool -> Bool
    Bool,
    Nat, // Natural Number
    Record(Fields),
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
        Ty { kind: Record(fields) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_record_type_equality() {
        // { 10, a=false }
        let mut fields1 = Fields::new();
        fields1.insert("0".to_string(), Box::new(Ty::new_nat()));
        fields1.insert("a".to_string(), Box::new(Ty::new_bool()));
        let record1 = Ty::new_record(fields1);

        // { 1, a=true }
        let mut fields2 = Fields::new();
        fields2.insert("0".to_string(), Box::new(Ty::new_nat()));
        fields2.insert("a".to_string(), Box::new(Ty::new_bool()));
        let record2 = Ty::new_record(fields2);

        // { a=true, 1 }
        let mut fields3 = Fields::new();
        fields3.insert("a".to_string(), Box::new(Ty::new_bool()));
        fields3.insert("0".to_string(), Box::new(Ty::new_nat()));
        let record3 = Ty::new_record(fields3);

        assert!(record1 == record2);
        assert!(record1 != record3);
    }
}
