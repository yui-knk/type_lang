use std::collections::HashMap;

use ty::Ty;

#[derive(Clone, Debug, PartialEq)]
pub struct Node {
    pub kind: Kind,
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
    Record(HashMap<String, Box<Node>>), // from label to value node
    Projection(Box<Node>, String), // Record, label
    If(Box<Node>, Box<Node>, Box<Node>), // cond, then_expr, else_expr
    Unit,
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

    pub fn new_projection(record: Node, label: String) -> Node {
        Node { kind: Projection(Box::new(record), label) }
    }

    pub fn new_record(fields: Vec<(Option<String>, Node)>) -> Node {
        let mut count = 0;
        let mut map = HashMap::new();

        for (name, node) in fields {
            let label = match name {
                Some(s) => s,
                None => count.to_string(),
            };

            map.insert(label, Box::new(node));
            count += 1;
        }

        Node { kind: Record(map) }
    }

    pub fn is_none_expression(&self) -> bool {
        match self.kind {
            NoneExpression => true,
            _ => false
        }
    }
}
