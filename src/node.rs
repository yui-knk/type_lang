#[derive(Debug, PartialEq)]
pub struct Node {
    pub kind: Kind,
}

#[derive(Debug, PartialEq)]
pub enum Kind {
    NoneExpression,
    Expression(Box<Node>),
    VarRef(String),
    Lambda(String, Box<Node>), // variable, body
    Bool(bool),
}

use self::Kind::*;

impl Node {
    pub fn new_none_expression() -> Node {
        Node { kind: NoneExpression }
    }

    pub fn new_expression(node: Node) -> Node {
        Node { kind: Expression(Box::new(node)) }
    }

    pub fn new_var_ref(str: String) -> Node {
        Node { kind: VarRef(str) }
    }

    pub fn new_lambda(var: String, node: Node) -> Node {
        Node { kind: Lambda(var, Box::new(node)) }
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
