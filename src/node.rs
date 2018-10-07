use ty::Ty;

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
    Tag(String, Box<Node>), // tag (inl|inr), value
    As(Box<Node>, Box<Ty>), // expression, ascribed type
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

    pub fn new_tag(s: String, node: Node) -> Node {
        Node { kind: Tag(s, Box::new(node)) }
    }

    pub fn new_projection(record: Node, label: String) -> Node {
        Node { kind: Projection(Box::new(record), label) }
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
}
