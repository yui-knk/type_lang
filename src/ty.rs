#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct Ty {
    pub kind: Kind
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
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

    pub fn iter(&self) -> ::std::slice::Iter<(String, Box<Ty>)> {
        self.elements.iter()
    }

    pub fn get(&self, k: &str) -> Option<&Box<Ty>>
    {
        for (i, (s, n)) in self.elements.iter().enumerate() {
            if s == k { return Some(n) }
            if i.to_string() == k { return Some(n) }
        }

        None
    }
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Kind {
    Arrow(Box<Ty>, Box<Ty>), // e.g. Bool -> Bool
    Bool,
    Nat, // Natural Number
    Top,
    Record(Fields),
    Variant(Fields),
    Unit, // the only value of Unit type is "unit"
    Ref(Box<Ty>), // `ref 1` has `Ref Nat` type
    Id(String), // type variable. (Type variable: 'X')
    All(String, Box<Ty>), // type variable, type. (Universal type)
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

    pub fn new_top() -> Ty {
        Ty { kind: Top }
    }

    pub fn new_unit() -> Ty {
        Ty { kind: Unit }
    }

    pub fn new_record(fields: Fields) -> Ty {
        Ty { kind: Record(fields) }
    }

    pub fn new_variant(fields: Fields) -> Ty {
        Ty { kind: Variant(fields) }
    }

    pub fn new_ref(ty: Ty) -> Ty {
        Ty { kind: Ref(Box::new(ty)) }
    }

    pub fn new_id(str: String) -> Ty {
        Ty { kind: Id(str) }
    }

    pub fn new_all(s: String, ty: Ty) -> Ty {
        Ty { kind: All(s, Box::new(ty)) }
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
