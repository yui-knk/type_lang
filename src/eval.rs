use node::{Node, Kind};
use value::Value;

pub struct Evaluator {
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedNode(String),
}

impl Evaluator {
    pub fn new() -> Evaluator {
        Evaluator {}
    }

    pub fn eval(&self, node: &Node) -> Result<Value, Error> {
        match node.kind {
            Kind::NoneExpression => self.eval_none_expression(node),
            Kind::Bool(_) => self.eval_bool(node),
            _ => Err(Error::UnexpectedNode(format!("{:?}", node)))
        }
    }

    fn eval_none_expression(&self, node: &Node) -> Result<Value, Error> {
        Ok(Value::new_none())
    }

    fn eval_bool(&self, node: &Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Bool(true)  => Ok(Value::new_true()),
            Kind::Bool(false) => Ok(Value::new_false()),
            _ => Err(Error::UnexpectedNode(format!("{:?}", node)))
        }
    }
}
