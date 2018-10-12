use ty::Ty;
use value::{Value, Fields as ValueFields};

#[derive(Clone, Debug, PartialEq)]
pub struct Node {
    pub kind: Kind,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Fields {
    elements: Vec<(String, Box<Node>)>
}

impl Fields {
    pub fn new() -> Fields {
        Fields { elements: Vec::new() }
    }

    pub fn insert(&mut self, k: String, v: Box<Node>) {
        self.elements.push((k, v))
    }

    pub fn iter(&self) -> ::std::slice::Iter<(String, Box<Node>)> {
        self.elements.iter()
    }

    pub fn get(&self, k: &str) -> Option<&Box<Node>>
    {
        for (i, (s, n)) in self.elements.iter().enumerate() {
            if s == k { return Some(n) }
            if i.to_string() == k { return Some(n) }
        }

        None
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Cases {
    elements: Vec<(String, (String, Box<Node>))> // (tag, (variable, body))
}

impl Cases {
    pub fn new() -> Cases {
        Cases { elements: Vec::new() }
    }

    pub fn insert(&mut self, tag: String, variable: String, body: Node) {
        self.elements.push((tag, (variable, Box::new(body))))
    }

    pub fn iter(&self) -> ::std::slice::Iter<(String, (String, Box<Node>))> {
        self.elements.iter()
    }

    pub fn get(&self, k: &str) -> Option<&(String, Box<Node>)>
    {
        for (i, (s, n)) in self.elements.iter().enumerate() {
            if s == k { return Some(n) }
            if i.to_string() == k { return Some(n) }
        }

        None
    }
}

#[derive(Debug, PartialEq)]
pub enum Error {
    CanNotConvertToValue(String),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    NoneExpression,
    VarRef(String),
    Lambda(String, Box<Node>, Box<Ty>), // variable, body, type of argument
    Let(String, Box<Node>, Box<Node>), // variable, bound value, body
    Apply(Box<Node>, Box<Node>),
    Bool(bool),
    Zero, // Natural Number is Zero or Succ(Natural Number)
    Succ(Box<Node>), // holds Zero or Succ(Natural Number)
    Pred(Box<Node>), // holds Zero or Succ(Natural Number)
    Iszero(Box<Node>), // operand
    Record(Fields), // from label to value node
    Projection(Box<Node>, String), // Record, label
    If(Box<Node>, Box<Node>, Box<Node>), // cond, then_expr, else_expr
    Unit,
    Tag(String, Box<Node>, Box<Ty>), // tag, value, type of variant
    Case(Box<Node>, Cases), // variant, (tag, (variable, body))
    As(Box<Node>, Box<Ty>), // expression, ascribed type
    Fix(Box<Node>), // generator node
    Ref(Box<Node>), // bound value
    Deref(Box<Node>), // reference value
    Assign(Box<Node>, Box<Node>), // reference, value
}

use self::Kind::*;

impl Node {
    pub fn new_none_expression() -> Node {
        Node { kind: NoneExpression }
    }

    pub fn new_var_ref(str: String) -> Node {
        Node { kind: VarRef(str) }
    }

    pub fn new_as(node: Node, ty: Ty) -> Node {
        Node { kind: As(Box::new(node), Box::new(ty)) }
    }

    pub fn new_lambda(var: String, node: Node, ty: Ty) -> Node {
        Node { kind: Lambda(var, Box::new(node), Box::new(ty)) }
    }

    pub fn new_let(var: String, bound_value: Node, body: Node) -> Node {
        Node { kind: Let(var, Box::new(bound_value), Box::new(body)) }
    }

    pub fn new_apply(node_1: Node, node_2: Node) -> Node {
        Node { kind: Apply(Box::new(node_1), Box::new(node_2)) }
    }

    pub fn new_iszero(node: Node) -> Node {
        Node { kind: Iszero(Box::new(node)) }
    }

    pub fn new_succ(node: Node) -> Node {
        Node { kind: Succ(Box::new(node)) }
    }

    pub fn new_pred(node: Node) -> Node {
        Node { kind: Pred(Box::new(node)) }
    }

    pub fn new_fix(node: Node) -> Node {
        Node { kind: Fix(Box::new(node)) }
    }

    pub fn new_ref(node: Node) -> Node {
        Node { kind: Ref(Box::new(node)) }
    }

    pub fn new_deref(node: Node) -> Node {
        Node { kind: Deref(Box::new(node)) }
    }

    pub fn new_assign(left: Node, right: Node) -> Node {
        Node { kind: Assign(Box::new(left), Box::new(right)) }
    }

    pub fn new_bool(bool: bool) -> Node {
        Node { kind: Bool(bool) }
    }

    pub fn new_unit() -> Node {
        Node { kind: Unit }
    }

    pub fn new_nat(mut i: u32) -> Node {
        let mut node = Node { kind: Zero };

        while i > 0 {
            node = Node { kind: Succ(Box::new(node)) };
            i -= 1;
        }

        node
    }

    pub fn new_if(cond: Node, then_expr: Node, else_expr: Node) -> Node {
        Node { kind: If(Box::new(cond), Box::new(then_expr), Box::new(else_expr)) }
    }

    pub fn new_tag(s: String, node: Node, ty: Ty) -> Node {
        Node { kind: Tag(s, Box::new(node), Box::new(ty)) }
    }

    pub fn new_case(node: Node, cases: Cases) -> Node {
        Node { kind: Case(Box::new(node), cases) }
    }

    pub fn new_projection(record: Node, label: String) -> Node {
        Node { kind: Projection(Box::new(record), label) }
    }

    pub fn new_record_from_fields(fields: Fields) -> Node {
        Node { kind: Record(fields) }
    }

    pub fn new_record(fields: Vec<(Option<String>, Node)>) -> Node {
        let mut count = 0;
        let mut vec = Vec::with_capacity(fields.len());

        for (name, node) in fields {
            let label = match name {
                Some(s) => s,
                None => count.to_string(),
            };

            vec.push((label, Box::new(node)));
            count += 1;
        }

        Node { kind: Record(Fields { elements: vec }) }
    }

    pub fn is_none_expression(&self) -> bool {
        match self.kind {
            NoneExpression => true,
            _ => false
        }
    }

    pub fn into_value(self) -> Result<Value, Error> {
        match self.kind {
            NoneExpression => Ok(Value::new_none()),
            Bool(b) => {
                if b {
                    Ok(Value::new_true())
                } else {
                    Ok(Value::new_false())
                }
            },
            Zero => self.into_nat_value(0),
            Succ(..) => self.into_nat_value(0),
            Tag(s, node, ty) => {
                let v = node.into_value()?;
                Ok(Value::new_tag(s, v, *ty))
            },
            Record(fields) => {
                let mut vf = ValueFields::new();

                for (s, node) in fields.iter() {
                    let v = node.clone().into_value()?;
                    vf.insert(s.clone(), Box::new(v));
                }

                Ok(Value::new_record(vf))
            },
            Unit => Ok(Value::new_unit()),
            Lambda(..) => Ok(Value::new_lambda(self)),
            _ => Err(Error::CanNotConvertToValue(format!("This is not a value node: {:?}", self)))
        }
    }

    fn into_nat_value(&self, i: u32) -> Result<Value, Error> {
        match self.kind {
            Zero => Ok(Value::new_nat(i)),
            Succ(ref node) => node.into_nat_value(i + 1),
            _ => Err(Error::CanNotConvertToValue(format!("This is not a nat value node: {:?}", self)))
        }
    }

    pub fn is_value(&self) -> bool {
        match self.kind {
            NoneExpression => true,
            Bool(..) => true,
            Zero => true,
            Succ(..) => true,
            Tag(_, ref node, _) => node.is_value(),
            Record(ref fields) => fields.iter().all(|(_, node)| node.is_value()),
            Unit => true,
            Lambda(..) => true,
            _ => false
        }
    }

    pub fn is_numericval(&self) -> bool {
        match self.kind {
            Zero => true,
            Succ(..) => true,
            _ => false
        }
    }
}
