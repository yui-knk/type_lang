use node::{Node, Kind};
use value::Value;

pub struct Evaluator {
}

impl Evaluator {
    pub fn new() -> Evaluator {
        Evaluator {}
    }

    pub fn eval(&self, node: &Node) -> Option<Value> {
        match node.kind {
            Kind::NoneExpression => self.eval_none_expression(node),
            Kind::Bool(_) => self.eval_bool(node),
            _ => None
        }
    }

    fn eval_none_expression(&self, node: &Node) -> Option<Value> {
        Some(Value::new_none())
    }

    fn eval_bool(&self, node: &Node) -> Option<Value> {
        match node.kind {
            Kind::Bool(true)  => Some(Value::new_true()),
            Kind::Bool(false) => Some(Value::new_false()),
            _ => unreachable!()
        }
    }
}
