#[derive(Clone, Debug, PartialEq)]
pub struct Node {
    pub kind: Kind,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    NoneExpression,
    VarRef(String),
    Lambda(String, Box<Node>), // variable, body
    Apply(Box<Node>, Box<Node>),
    Bool(bool),
}

use self::Kind::*;

impl Node {
    pub fn new_none_expression() -> Node {
        Node { kind: NoneExpression }
    }

    pub fn new_var_ref(str: String) -> Node {
        Node { kind: VarRef(str) }
    }

    pub fn new_lambda(var: String, node: Node) -> Node {
        Node { kind: Lambda(var, Box::new(node)) }
    }

    pub fn new_apply(node_1: Node, node_2: Node) -> Node {
        Node { kind: Apply(Box::new(node_1), Box::new(node_2)) }
    }

    pub fn new_bool(bool: bool) -> Node {
        Node { kind: Bool(bool) }
    }

    pub fn is_none_expression(&self) -> bool {
        match self.kind {
            NoneExpression => true,
            _ => false
        }
    }
}
