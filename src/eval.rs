use node::{Node, Kind};
use value::{Value};

struct Env {
    // Mapping from variable to value node.
    // Use Vec as a stack.
    //
    // Value may be shared multi lambda bodies.
    stack: Vec<(String, Node)>,
}

pub struct Evaluator {
    env: Env,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedNode(String),
    VariableNotFound(String),
    NotApplyable(String),
    IndexError(String),
    CanNotConvertToValue(String),
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

    fn find_by_variable(&self, variable: &str) -> Option<Node> {
        for (str, node) in self.stack.iter().rev() {
            if str == variable {
                return Some(node.clone());
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
        let value_node = self._eval(node)?;

        if value_node.is_value() {
            Ok(self.into_value(value_node).unwrap())
        } else {
            Err(Error::UnexpectedNode(format!("This is not a value node: {:?}", value_node)))
        }
    }

    fn into_value(&self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::NoneExpression => Ok(Value::new_none()),
            Kind::Bool(b) => {
                if b {
                    Ok(Value::new_true())
                } else {
                    Ok(Value::new_false())
                }
            },
            Kind::Zero => self.into_nat_value(&node, 0),
            Kind::Succ(..) => self.into_nat_value(&node, 0),
            Kind::Lambda(..) => Ok(Value::new_lambda(node)),
            _ => Err(Error::CanNotConvertToValue(format!("This is not a value node: {:?}", node)))
        }
    }

    fn into_nat_value(&self, node: &Node, i: u32) -> Result<Value, Error> {
        match node.kind {
            Kind::Zero => Ok(Value::new_nat(i)),
            Kind::Succ(ref node2) => self.into_nat_value(node2, i + 1),
            _ => Err(Error::CanNotConvertToValue(format!("This is not a nat value node: {:?}", node)))
        }
    }

    fn _eval(&mut self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::NoneExpression => self.eval_none_expression(node),
            Kind::Bool(_) => self.eval_bool(node),
            Kind::Zero => self.eval_zero(node),
            Kind::Succ(_) => self.eval_succ(node),
            Kind::Pred(_) => self.eval_pred(node),
            Kind::Apply(..) => self.eval_apply(node),
            Kind::Let(..) => self.eval_let(node),
            Kind::Lambda(..) => self.eval_lambda(node),
            Kind::VarRef(..) => self.eval_var_ref(node),
            Kind::If(..) => self.eval_if(node),
            Kind::Iszero(..) => self.eval_iszero(node),
            // _ => panic!("")
        }
    }

    fn eval_none_expression(&self, node: Node) -> Result<Node, Error> {
        Ok(node)
    }

    fn eval_let(&mut self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::Let(variable, bound, body) => {
                let bound_value = self._eval(*bound)?;
                self.env.push(variable, bound_value);
                let body_value = self._eval(*body)?;
                self.env.pop();
                Ok(body_value)
            },
            _ => Err(Error::UnexpectedNode(format!("eval_let {:?}", node)))
        }
    }

    fn eval_apply(&mut self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::Apply(rec, arg) => {
                let arg_val = self._eval(*arg)?;
                let rec_val = self._eval(*rec)?;
                let (variable, body) = match rec_val.kind {
                    Kind::Lambda(v, b, _) => (v, b),
                    _ => return Err(Error::NotApplyable(format!("{:?} is not applyable", rec_val.kind)))
                };

                self.env.push(variable, arg_val);
                let rec_val = self._eval(*body)?;
                self.env.pop();
                Ok(rec_val)
            },
            _ => Err(Error::UnexpectedNode(format!("eval_ref {:?}", node)))
        }
    }

    fn eval_var_ref(&mut self, node: Node) -> Result<Node, Error> {
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

    fn eval_bool(&self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::Bool(..)  => Ok(node),
            _ => Err(Error::UnexpectedNode(format!("eval_bool {:?}", node)))
        }
    }

    fn eval_zero(&self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::Zero => Ok(node),
            _ => Err(Error::UnexpectedNode(format!("eval_zero {:?}", node)))
        }
    }

    fn eval_succ(&mut self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::Succ(n) => {
                let n_val = self._eval(*n)?;

                if n_val.is_numericval() {
                    Ok(Node::new_succ(n_val))
                } else {
                    Err(Error::UnexpectedNode(format!("eval_succ {:?}", n_val)))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_succ {:?}", node)))
        }
    }

    fn eval_pred(&mut self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::Pred(n) => {
                let n_val = self._eval(*n)?;

                match n_val.kind {
                    Kind::Zero => {
                        Ok(Node::new_nat(0))
                    },
                    Kind::Succ(n) => {
                        Ok(*n)
                    },
                    _ => Err(Error::UnexpectedNode(format!("eval_pred {:?}", n_val)))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_pred {:?}", node)))
        }
    }

    fn eval_lambda(&self, node: Node) -> Result<Node, Error> {
        Ok(node)
    }

    fn eval_iszero(&mut self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::Iszero(n) => {
                let error_message = format!("eval_iszero {:?}", n);
                let n_val = self._eval(*n)?;

                match n_val.kind {
                    Kind::Zero => Ok(Node::new_bool(true)),
                    Kind::Succ(_) => Ok(Node::new_bool(false)),
                    _ => Err(Error::UnexpectedNode(error_message))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_iszero {:?}", node)))
        }
    }

    fn eval_if(&mut self, node: Node) -> Result<Node, Error> {
        match node.kind {
            Kind::If(cond, then_expr, else_expr) => {
                let cond_val = self._eval(*cond)?;

                match cond_val.kind {
                    Kind::Bool(b) => {
                        if b {
                            self._eval(*then_expr)
                        } else {
                            self._eval(*else_expr)
                        }
                    },
                    _ => Err(Error::UnexpectedNode(format!("eval_if {:?}", cond_val)))
                }
            }
            _ => Err(Error::UnexpectedNode(format!("eval_if {:?}", node)))
        }
    }
}

#[cfg(test)]
mod tests_env {
    use super::*;

    #[test]
    fn test_find_by_variable() {
        let mut env = Env::new();
        env.push("x".to_string(), Node::new_bool(false));

        assert_eq!(env.find_by_variable(&"y".to_string()), None);
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(Node::new_bool(false)));

        env.push("y".to_string(), Node::new_bool(true));
        assert_eq!(env.find_by_variable(&"y".to_string()), Some(Node::new_bool(true)));
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(Node::new_bool(false)));

        env.pop();
        env.push("x".to_string(), Node::new_bool(true));
        assert_eq!(env.find_by_variable(&"y".to_string()), None);
        assert_eq!(env.find_by_variable(&"x".to_string()), Some(Node::new_bool(true)));

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
    fn test_eval_let() {
        let result = eval_string(" let x = 1 in x ".to_string());
        assert_eq!(result, Ok(Value::new_nat(1)));

        let result = eval_string(" let x = 0 in iszero x ".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string(" let x = 1 in false ".to_string());
        assert_eq!(result, Ok(Value::new_false()));
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
        let result = eval_string("-> x : Bool { x }.(false)".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("-> x : Bool { -> x : Bool { x }.(x) }.(true)".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string("-> x : Bool { -> x : Bool { x }.(false) }.(true)".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("-> x : Bool -> Bool { x }.(-> y : Bool { y }).(true)".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string("-> x : Bool -> Bool{ x }.( -> y : Bool { false } )".to_string());
        let node_false = Node::new_bool(false);
        // Type of lambda node is a type of arg.
        let ty = Ty::new_bool();
        let lambda = Node::new_lambda("y".to_string(), node_false, ty);
        assert_eq!(result, Ok(Value::new_lambda(lambda)));
    }

    #[test]
    fn test_eval_associativity() {
        let result = eval_string("succ 0".to_string());
        assert_eq!(result, Ok(Value::new_nat(1)));

        let result = eval_string("pred succ 0".to_string());
        assert_eq!(result, Ok(Value::new_nat(0)));

        let result = eval_string("iszero succ 0".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("iszero pred succ 0".to_string());
        assert_eq!(result, Ok(Value::new_true()));
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
