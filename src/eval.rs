use std::collections::HashMap;

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
    NotApplyable(String),
    UnexpectedValue(String)
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
            Kind::Zero => self.eval_zero(node),
            Kind::Succ(_) => self.eval_succ(node),
            Kind::Pred(_) => self.eval_pred(node),
            Kind::Apply(..) => self.eval_apply(node),
            Kind::Lambda(..) => self.eval_lambda(node),
            Kind::VarRef(..) => self.eval_var_ref(node),
            Kind::If(..) => self.eval_if(node),
            Kind::Iszero(..) => self.eval_iszero(node),
            Kind::Record(..) => self.eval_record(node),
            // _ => panic!("")
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
                    Kind::Lambda(v, b, _) => (v, b),
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

    fn eval_zero(&self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Zero => Ok(Value::new_nat(0)),
            _ => Err(Error::UnexpectedNode(format!("eval_zero {:?}", node)))
        }
    }

    fn eval_succ(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Succ(n) => {
                let n_val = self.eval(*n)?;

                match n_val.kind {
                    ValueKind::Nat(i) => {
                        Ok(Value::new_nat(i + 1))
                    },
                    _ => Err(Error::UnexpectedValue(format!("eval_succ {:?}", n_val)))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_succ {:?}", node)))
        }
    }

    fn eval_pred(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Pred(n) => {
                let n_val = self.eval(*n)?;

                match n_val.kind {
                    ValueKind::Nat(i) => {
                        let j = if i > 0 {
                            i - 1
                        } else {
                            0
                        };
                        Ok(Value::new_nat(j))
                    },
                    _ => Err(Error::UnexpectedValue(format!("eval_pred {:?}", n_val)))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_pred {:?}", node)))
        }
    }

    fn eval_lambda(&self, node: Node) -> Result<Value, Error> {
        Ok(Value::new_lambda(node))
    }

    fn eval_record(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Record(fields) => {
                let mut field_values = HashMap::new();

                for (s, node) in fields {
                    let field_value = self.eval(*node)?;
                    field_values.insert(s.clone(), Box::new(field_value));
                }

                Ok(Value::new_record(field_values))
            },
            _ => Err(Error::UnexpectedNode(format!("eval_record {:?}", node)))
        }
    }

    fn eval_iszero(&self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Iszero(n) => {
                match n.kind {
                    Kind::Zero => Ok(Value::new_true()),
                    Kind::Succ(_) => Ok(Value::new_false()),
                    _ => Err(Error::UnexpectedNode(format!("eval_iszero {:?}", n)))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_iszero {:?}", node)))
        }
    }

    fn eval_if(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::If(cond, then_expr, else_expr) => {
                let cond_val = self.eval(*cond)?;

                match cond_val.kind {
                    ValueKind::True => {
                        self.eval(*then_expr)
                    },
                    ValueKind::False => {
                        self.eval(*else_expr)
                    },
                    _ => Err(Error::UnexpectedValue(format!("eval_if {:?}", cond_val)))
                }
            }
            _ => Err(Error::UnexpectedNode(format!("eval_if {:?}", node)))
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
    use ty::{Ty};
    use type_check::{TypeChecker};

    fn eval_string(str: String) -> Result<Value, Error> {
        let mut parser = Parser::new(str);
        let node = parser.parse().unwrap();
        let mut type_checker = TypeChecker::new();
        let _ = type_checker.check(&node).unwrap();
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
    fn test_eval_nat() {
        let result = eval_string("10".to_string());
        assert_eq!(result, Ok(Value::new_nat(10)));
    }

    #[test]
    fn test_eval_iszero() {
        let result = eval_string("iszero 0".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string("iszero 1".to_string());
        assert_eq!(result, Ok(Value::new_false()));
    }

    #[test]
    fn test_eval_succ() {
        let result = eval_string("succ 0".to_string());
        assert_eq!(result, Ok(Value::new_nat(1)));

        let result = eval_string("succ 1".to_string());
        assert_eq!(result, Ok(Value::new_nat(2)));

        let result = eval_string("succ 2".to_string());
        assert_eq!(result, Ok(Value::new_nat(3)));

        let result = eval_string("succ succ 3".to_string());
        assert_eq!(result, Ok(Value::new_nat(5)));
    }

    #[test]
    fn test_eval_pred() {
        let result = eval_string("pred 0".to_string());
        assert_eq!(result, Ok(Value::new_nat(0)));

        let result = eval_string("pred 1".to_string());
        assert_eq!(result, Ok(Value::new_nat(0)));

        let result = eval_string("pred 2".to_string());
        assert_eq!(result, Ok(Value::new_nat(1)));

        let result = eval_string("pred pred 3".to_string());
        assert_eq!(result, Ok(Value::new_nat(1)));
    }

    #[test]
    fn test_eval_succ_pred() {
        let result = eval_string("succ pred 0".to_string());
        assert_eq!(result, Ok(Value::new_nat(1)));

        let result = eval_string("pred succ 0".to_string());
        assert_eq!(result, Ok(Value::new_nat(0)));

        let result = eval_string("succ pred pred succ succ pred 3".to_string());
        assert_eq!(result, Ok(Value::new_nat(3)));
    }

    #[test]
    fn test_eval_record() {
        use std::collections::HashMap;

        let result = eval_string(" {10, a=false, true} ".to_string());
        let mut fields = HashMap::new();

        fields.insert("0".to_string(), Box::new(Value::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Value::new_false()));
        fields.insert("2".to_string(), Box::new(Value::new_true()));

        assert_eq!(result, Ok(Value::new_record(fields)));
    }

    #[test]
    fn test_eval_lambda() {
        let result = eval_string("-> x : Bool -> Bool { x }".to_string());
        let var_ref = Node::new_var_ref("x".to_string());
        let ty = Ty::new_arrow(Ty::new_bool(), Ty::new_bool());
        let lambda = Node::new_lambda("x".to_string(), var_ref, ty);

        assert_eq!(result, Ok(Value::new_lambda(lambda)));
    }

    #[test]
    fn test_eval_appy() {
        let result = eval_string("(-> x : Bool { x } false)".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("(-> x : Bool { (-> x : Bool { x } x) } true)".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string("(-> x : Bool { (-> x : Bool { x } false) } true)".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("((-> x : Bool -> Bool { x } -> y : Bool { y }) true)".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string("(-> x : Bool -> Bool{ x } -> y : Bool { false } )".to_string());
        let node_false = Node::new_bool(false);
        // Type of lambda node is a type of arg.
        let ty = Ty::new_bool();
        let lambda = Node::new_lambda("y".to_string(), node_false, ty);
        assert_eq!(result, Ok(Value::new_lambda(lambda)));
    }

    #[test]
    fn test_eval_if() {
        let result = eval_string("if true then false else true".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("if false then false else true".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string(r#"
            if false
            then false
            else true
        "#.to_string());
        assert_eq!(result, Ok(Value::new_true()));
    }

    // TODO: type_check returns `VariableNotFound("y")` error
    // #[test]
    // fn test_eval_variable_not_found() {
    //     let result = eval_string("(-> x : Bool { y } false)".to_string());
    //     assert_eq!(result, Err(Error::VariableNotFound("y".to_string())));
    // }
}
