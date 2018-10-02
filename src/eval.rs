use std::collections::HashMap;

use node::{Node, Kind};
use value::Value;

struct Env {
    // Mapping from variable to "value node"
    // Use Vec as a stack
    //
    // TODO: Node may be shared multi lambda bodies?
    stack: Vec<(String, Node)>
}

pub struct Evaluator {
    env: Env,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedNode(String),
}

impl Env {
    fn new() -> Env {
        Env { stack: Vec::new() }
    }

    fn push(&mut self, variable: String, node: Node) {
        self.stack.push((variable, node));
    }

    fn pop(&mut self) {
        if self.stack.pop().is_none() {
            eprintln!("empty stack is popped.");
        }
    }

    fn find_by_variable(&self, variable: &str) -> Option<&Node> {
        for (str, node) in self.stack.iter().rev() {
            if str == variable {
                return Some(node);
            }
        }

        None
    }
}

impl Evaluator {
    pub fn new() -> Evaluator {
        Evaluator { env: Env::new() }
    }

    pub fn eval(&self, node: &Node) -> Result<Value, Error> {
        match node.kind {
            Kind::NoneExpression => self.eval_none_expression(node),
            Kind::Bool(_) => self.eval_bool(node),
            Kind::Lambda(..) => self.eval_lambda(node),
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

    fn eval_lambda(&self, _node: &Node) -> Result<Value, Error> {
        Ok(Value::new_lambda())
    }

    fn node_is_value(node: &Node) -> bool {
        match node.kind {
            Kind::Lambda(..) => true,
            Kind::Bool(..) => true,
            _ => false
        }
    }
}

#[cfg(test)]
mod tests_env {
    use super::*;
    use node::{Node};

    #[test]
    fn test_find_by_variable() {
        let mut env = Env::new();
        env.push("x".to_string(), Node::new_bool(false));

        assert_eq!(env.find_by_variable(&"y".to_string()), None);
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(&Node::new_bool(false)));

        env.push("y".to_string(), Node::new_bool(true));
        assert_eq!(env.find_by_variable(&"y".to_string()), Some(&Node::new_bool(true)));
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(&Node::new_bool(false)));

        env.pop();
        env.push("x".to_string(), Node::new_bool(true));
        assert_eq!(env.find_by_variable(&"y".to_string()), None);
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(&Node::new_bool(true)));

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

    #[test]
    fn test_eval_lambda() {
        let result = eval_string("-> x { x }".to_string());

        assert_eq!(result, Ok(Value::new_lambda()));
    }
}
