use node::{Node, Kind};
use value::{Value, Kind as ValueKind};

struct Env {
    // Mapping from variable to value.
    // Use Vec as a stack.
    //
    // Value may be shared multi lambda bodies.
    stack: Vec<(String, Value)>
}

pub struct Evaluator {
    env: Env,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedNode(String),
    VariableNotFound(String),
    NotApplyable(String)
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

    fn find_by_variable(&self, variable: &str) -> Option<Value> {
        for (str, value) in self.stack.iter().rev() {
            if str == variable {
                return Some(value.clone());
            }
        }

        None
    }
}

impl Evaluator {
    pub fn new() -> Evaluator {
        Evaluator { env: Env::new() }
    }

    pub fn eval(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::NoneExpression => self.eval_none_expression(node),
            Kind::Bool(_) => self.eval_bool(node),
            Kind::Apply(..) => self.eval_apply(node),
            Kind::Lambda(..) => self.eval_lambda(node),
            Kind::VarRef(..) => self.eval_var_ref(node),
        }
    }

    fn eval_none_expression(&self, _node: Node) -> Result<Value, Error> {
        Ok(Value::new_none())
    }

    fn eval_apply(&mut self, node: Node) -> Result<Value, Error> {
        let error_message = format!("eval_apply {:?}", node);

        match node.kind {
            Kind::Apply(rec, arg) => {
                let arg_val = self.eval(*arg)?;
                let rec_val = self.eval(*rec)?;
                let rec_val_kind = rec_val.kind;
                let rec_node = match rec_val_kind {
                    ValueKind::Lambda(n) => n,
                    _ => return Err(Error::NotApplyable(format!("{:?} is not applyable", rec_val_kind)))
                };
                let (variable, body) = match rec_node.kind {
                    Kind::Lambda(v, b) => (v, b),
                    _ => return Err(Error::UnexpectedNode(error_message))
                };

                self.env.push(variable, arg_val);
                let rec_val = self.eval(*body)?;
                self.env.pop();
                Ok(rec_val)
            },
            _ => Err(Error::UnexpectedNode(error_message))
        }
    }

    fn eval_var_ref(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::VarRef(variable) => {
                match self.env.find_by_variable(&variable) {
                    Some(v) => Ok(v),
                    None => Err(Error::VariableNotFound(variable.clone()))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_var_ref {:?}", node)))
        }
    }

    fn eval_bool(&self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Bool(true)  => Ok(Value::new_true()),
            Kind::Bool(false) => Ok(Value::new_false()),
            _ => Err(Error::UnexpectedNode(format!("eval_bool {:?}", node)))
        }
    }

    fn eval_lambda(&self, node: Node) -> Result<Value, Error> {
        Ok(Value::new_lambda(node))
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
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(Value::new_false()));

        env.push("y".to_string(), Value::new_true());
        assert_eq!(env.find_by_variable(&"y".to_string()), Some(Value::new_true()));
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(Value::new_false()));

        env.pop();
        env.push("x".to_string(), Value::new_true());
        assert_eq!(env.find_by_variable(&"y".to_string()), None);
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(Value::new_true()));

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
        let mut eval = Evaluator::new();
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

    #[test]
    fn test_eval_appy() {
        let result = eval_string("(-> x { x } false)".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("(-> x { (-> x { x } x) } true)".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string("(-> x { (-> x { x } false) } true)".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("((-> x { x } -> y { y }) true)".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string("((-> x { x } -> y { y }) -> z { false })".to_string());
        let node_false = Node::new_bool(false);
        let lambda = Node::new_lambda("z".to_string(), node_false);
        assert_eq!(result, Ok(Value::new_lambda(lambda)));
    }

    #[test]
    fn test_eval_variable_not_found() {
        let result = eval_string("(-> x { y } false)".to_string());
        assert_eq!(result, Err(Error::VariableNotFound("y".to_string())));
    }
}
