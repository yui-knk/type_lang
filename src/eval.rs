use node::{Node, Kind};
use value::Value;

struct Env {
    // Mapping from variable to value
    // Use Vec as a stack
    //
    // TODO: Value may be shared multi lambda bodies?
    stack: Vec<(String, Value)>
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

    fn push(&mut self, variable: String, value: Value) {
        self.stack.push((variable, value));
    }

    fn pop(&mut self) {
        if self.stack.pop().is_none() {
            eprintln!("empty stack is popped.");
        }
    }

    fn find_by_variable(&self, variable: &str) -> Option<&Value> {
        for (str, value) in self.stack.iter().rev() {
            if str == variable {
                return Some(value);
            }
        }

        None
    }
}

impl Evaluator {
    pub fn new() -> Evaluator {
        Evaluator { env: Env::new() }
    }

    pub fn eval(&self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::NoneExpression => self.eval_none_expression(node),
            Kind::Bool(_) => self.eval_bool(node),
            Kind::Lambda(..) => self.eval_lambda(node),
            _ => Err(Error::UnexpectedNode(format!("{:?}", node)))
        }
    }

    fn eval_none_expression(&self, _node: Node) -> Result<Value, Error> {
        Ok(Value::new_none())
    }

    fn eval_bool(&self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Bool(true)  => Ok(Value::new_true()),
            Kind::Bool(false) => Ok(Value::new_false()),
            _ => Err(Error::UnexpectedNode(format!("{:?}", node)))
        }
    }

    fn eval_lambda(&self, node: Node) -> Result<Value, Error> {
        Ok(Value::new_lambda(node))
    }

    fn node_is_value(node: Node) -> bool {
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
    use value::Value;

    #[test]
    fn test_find_by_variable() {
        let mut env = Env::new();
        env.push("x".to_string(), Value::new_false());

        assert_eq!(env.find_by_variable(&"y".to_string()), None);
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(&Value::new_false()));

        env.push("y".to_string(), Value::new_true());
        assert_eq!(env.find_by_variable(&"y".to_string()), Some(&Value::new_true()));
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(&Value::new_false()));

        env.pop();
        env.push("x".to_string(), Value::new_true());
        assert_eq!(env.find_by_variable(&"y".to_string()), None);
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(&Value::new_true()));

    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use value::{Value};
    use parser::{Parser};
    use node::{Node};

    fn eval_string(str: String) -> Result<Value, Error> {
        let mut parser = Parser::new(str);
        let node = parser.parse().unwrap();
        let eval = Evaluator::new();
        eval.eval(node)
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
        let var_ref = Node::new_var_ref("x".to_string());
        let lambda = Node::new_lambda("x".to_string(), var_ref);

        assert_eq!(result, Ok(Value::new_lambda(lambda)));
    }
}
