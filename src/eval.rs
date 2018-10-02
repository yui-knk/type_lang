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

#[cfg(test)]
mod tests {
    use super::*;
    use value::{Value};
    use parser::{Parser};

    fn eval_string(str: String) -> Result<Value, Error> {
        let mut parser = Parser::new(str);
        let noed = parser.parse().unwrap();
        let eval = Evaluator::new();
        eval.eval(&noed)
    }

    #[test]
    fn test_eval_false() {
        let result = eval_string("false".to_string());

        assert_eq!(result, Ok(Value::new_false()));
    }

    #[test]
    fn test_eval_true() {
        let result = eval_string("true".to_string());

        assert_eq!(result, Ok(Value::new_true()));
    }
}
