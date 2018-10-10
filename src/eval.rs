use node::{Node, Kind, Fields as NodeFields, Cases};
use value::{Value, Kind as ValueKind, Fields};

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
    UnexpectedValue(String),
    IndexError(String),
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
            Kind::Let(..) => self.eval_let(node),
            Kind::Lambda(..) => self.eval_lambda(node),
            Kind::VarRef(..) => self.eval_var_ref(node),
            Kind::If(..) => self.eval_if(node),
            Kind::Iszero(..) => self.eval_iszero(node),
            Kind::Record(..) => self.eval_record(node),
            Kind::Projection(..) => self.eval_projection(node),
            Kind::Unit => self.eval_unit(node),
            Kind::As(..) => self.eval_as(node),
            Kind::Tag(..) => self.eval_tag(node),
            Kind::Case(..) => self.eval_case(node),
            Kind::Fix(..) => self.eval_fix(node),
            // _ => panic!("")
        }
    }

    fn eval_none_expression(&self, _node: Node) -> Result<Value, Error> {
        Ok(Value::new_none())
    }

    fn eval_let(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Let(variable, bound, body) => {
                let bound_value = self.eval(*bound)?;
                self.env.push(variable, bound_value);
                let body_value = self.eval(*body)?;
                self.env.pop();
                Ok(body_value)
            },
            _ => Err(Error::UnexpectedNode(format!("eval_let {:?}", node)))
        }
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

    fn eval_unit(&self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Unit => Ok(Value::new_unit()),
            _ => Err(Error::UnexpectedNode(format!("eval_unit {:?}", node)))
        }
    }

    fn eval_as(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::As(expr, _) => self.eval(*expr),
            _ => Err(Error::UnexpectedNode(format!("eval_as {:?}", node)))
        }
    }

    fn eval_tag(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Tag(s, node, ty) => {
                let value = self.eval(*node)?;
                Ok(Value::new_tag(s, value, *ty))
            },
            _ => Err(Error::UnexpectedNode(format!("eval_tag {:?}", node)))
        }

    }

    fn replace_variable_with_fix_node(&self, variable: &str, fix_node: &Node, node: Node) -> Node {
        match node.kind {
              Kind::NoneExpression
            | Kind::Bool(..)
            | Kind::Zero
            | Kind::Unit => {
                node
            },
            Kind::Succ(arg) => {
                Node::new_succ(
                    self.replace_variable_with_fix_node(variable, fix_node, *arg)
                )
            },
            Kind::Pred(arg) => {
                Node::new_pred(
                    self.replace_variable_with_fix_node(variable, fix_node, *arg)
                )
            },
            Kind::Apply(rec, arg) => {
                let rec2 = self.replace_variable_with_fix_node(variable, fix_node, *rec);
                let arg2 = self.replace_variable_with_fix_node(variable, fix_node, *arg);
                Node::new_apply(rec2, arg2)
            },
            Kind::Let(s, bound, body) => {
                if s == variable {
                    // variable is newly bound, so need not to replace.
                    Node::new_let(s, *bound, *body)
                } else {
                    let bound2 = self.replace_variable_with_fix_node(variable, fix_node, *bound);
                    let body2 = self.replace_variable_with_fix_node(variable, fix_node, *body);
                    Node::new_let(s, bound2, body2)
                }
            },
            Kind::Lambda(s, body, ty) => {
                if s == variable {
                    // variable is newly bound, so need not to replace.
                    Node::new_lambda(s, *body, *ty)
                } else {
                    let body2 = self.replace_variable_with_fix_node(variable, fix_node, *body);
                    Node::new_lambda(s, body2, *ty)
                }
            },
            Kind::VarRef(ref s) => {
                if s == variable {
                    fix_node.clone()
                } else {
                    node.clone()
                }
            },
            Kind::If(cond, then_expr, else_expr) => {
                let c = self.replace_variable_with_fix_node(variable, fix_node, *cond);
                let t = self.replace_variable_with_fix_node(variable, fix_node, *then_expr);
                let e = self.replace_variable_with_fix_node(variable, fix_node, *else_expr);
                Node::new_if(c, t, e)
            },
            Kind::Iszero(op) => {
                let op2 = self.replace_variable_with_fix_node(variable, fix_node, *op);
                Node::new_iszero(op2)
            },
            Kind::Record(fields) => {
                let mut fields2 = NodeFields::new();

                for (s, n) in fields.iter() {
                    fields2.insert(
                        s.to_string(),
                        Box::new(self.replace_variable_with_fix_node(variable, fix_node, *n.clone()))
                    );
                }

                Node::new_record_from_fields(fields2)
            },
            Kind::Projection(record, s) => {
                let record2 = self.replace_variable_with_fix_node(variable, fix_node, *record);
                Node::new_projection(record2, s)
            },
            Kind::Tag(s, value, ty) => {
                let value2 = self.replace_variable_with_fix_node(variable, fix_node, *value);
                Node::new_tag(s, value2, *ty)
            },
            Kind::Case(variant, cases) => {
                let mut cases2 = Cases::new();
                let variant2 = self.replace_variable_with_fix_node(variable, fix_node, *variant);
                for (tag, (var, body)) in cases.iter() {
                    if *var == variable {
                        // variable is newly bound, so need not to replace.
                        cases2.insert(tag.to_string(), var.to_string(), *body.clone());
                    } else {
                        cases2.insert(
                            tag.to_string(), var.to_string(),
                            self.replace_variable_with_fix_node(variable, fix_node, *body.clone())
                        );
                    }
                }

                Node::new_case(variant2, cases2)
            },
            Kind::As(expr, ty) => {
                let expr2 = self.replace_variable_with_fix_node(variable, fix_node, *expr);
                Node::new_as(expr2, *ty)
            },
            Kind::Fix(generator) => {
                let generator2 = self.replace_variable_with_fix_node(variable, fix_node, *generator);
                Node::new_fix(generator2)
            },
            // _ => panic!("")
        }
    }

    fn eval_fix(&mut self, fix_node: Node) -> Result<Value, Error> {
        match fix_node.clone().kind {
            Kind::Fix(node) => {
                let node_value = self.eval(*node)?;
                let node2 = match node_value.clone().kind {
                    ValueKind::Lambda(n) => n,
                    _ => return Err(Error::NotApplyable(format!("{:?} is not applyable", node_value.kind)))
                };
                let (variable, body) = match node2.kind {
                    Kind::Lambda(v, b, _) => (v, b),
                    _ => return Err(Error::UnexpectedNode(format!("eval_fix expects Lambda node: {:?}", node2)))
                };

                let replaced = self.replace_variable_with_fix_node(&variable, &fix_node, *body);
                let replaced_val = self.eval(replaced)?;
                Ok(replaced_val)
            },
            _ => Err(Error::UnexpectedNode(format!("eval_fix expects Fix node: {:?}", fix_node)))
        }
    }

    fn eval_case(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Case(variant, cases) => {
                let variant_value = self.eval(*variant)?;

                match variant_value.kind {
                    ValueKind::Tag(s, v, _) => {
                       let case_node_opt = cases.get(&s);

                       match case_node_opt {
                            Some((var, case_node)) => {
                                self.env.push(var.clone(), *v);
                                let case_value = self.eval(*case_node.clone())?;
                                self.env.pop();
                                Ok(case_value)
                            },
                            None => Err(Error::IndexError(format!("eval_case {:?}", s)))
                       }
                    },
                    _ => Err(Error::UnexpectedValue(format!("eval_case {:?}", variant_value)))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_case {:?}", node)))
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
        let field_values = self._eval_record(node)?;
        Ok(Value::new_record(field_values))
    }

    fn _eval_record(&mut self, node: Node) -> Result<Fields, Error> {
        match node.kind {
            Kind::Record(fields) => {
                let mut field_values = Fields::new();

                for (s, node) in fields.iter() {
                    let field_value = self.eval(*node.clone())?;
                    field_values.insert(s.clone(), Box::new(field_value));
                }

                Ok(field_values)
            },
            _ => Err(Error::UnexpectedNode(format!("eval_record {:?}", node)))
        }
    }

    fn eval_projection(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Projection(node, label) => {
                let records = self._eval_record(*node)?;
                let value = records.get(&label);

                match value {
                    Some(v) => Ok(*v.clone()),
                    None => Err(Error::IndexError(format!("eval_projection {:?}", label)))
                }
            },
            _ => Err(Error::UnexpectedNode(format!("eval_projection {:?}", node)))
        }
    }

    fn eval_iszero(&mut self, node: Node) -> Result<Value, Error> {
        match node.kind {
            Kind::Iszero(n) => {
                let error_message = format!("eval_iszero {:?}", n);
                let n_val = self.eval(*n)?;

                match n_val.kind {
                    ValueKind::Nat(0) => Ok(Value::new_true()),
                    ValueKind::Nat(_) => Ok(Value::new_false()),
                    _ => Err(Error::UnexpectedNode(error_message))
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
    use ty::{Ty, Fields as TyFields};
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
    fn test_eval_unit() {
        let result = eval_string("unit".to_string());

        assert_eq!(result, Ok(Value::new_unit()));
    }

    #[test]
    fn test_eval_as() {
        let result = eval_string("false as Bool".to_string());

        assert_eq!(result, Ok(Value::new_false()));
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
    fn test_eval_variant() {
        let result = eval_string("<a=1> as <a:Nat, b:Bool>".to_string());
        let mut fields = TyFields::new();

        fields.insert("a".to_string(), Box::new(Ty::new_nat()));
        fields.insert("b".to_string(), Box::new(Ty::new_bool()));

        assert_eq!(result, Ok(Value::new_tag(
            "a".to_string(),
            Value::new_nat(1),
            Ty::new_variant(fields)
        )));
    }

    #[test]
    fn test_eval_record() {
        let result = eval_string(" {10, a=false, true} ".to_string());
        let mut fields = Fields::new();

        fields.insert("0".to_string(), Box::new(Value::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Value::new_false()));
        fields.insert("2".to_string(), Box::new(Value::new_true()));

        assert_eq!(result, Ok(Value::new_record(fields)));
    }

    #[test]
    fn test_eval_projection() {
        let result = eval_string(" {10, a=false, true}.a ".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string(" {10, a=false, true}.0 ".to_string());
        assert_eq!(result, Ok(Value::new_nat(10)));

        let result = eval_string(" {10, a=false, true}.1 ".to_string());
        assert_eq!(result, Ok(Value::new_false()));
    }

    #[test]
    fn test_eval_case() {
        let result = eval_string("case <a=1>     as <a:Nat, b:Bool> of <a=x> => x | <b=y> => 2".to_string());
        assert_eq!(result, Ok(Value::new_nat(1)));

        let result = eval_string("case <b=false> as <a:Nat, b:Bool> of <a=x> => x | <b=y> => 2".to_string());
        assert_eq!(result, Ok(Value::new_nat(2)));

        let result = eval_string("case <a=1>     as <a:Nat, b:Bool> of <a=x> => true | <b=y> => y".to_string());
        assert_eq!(result, Ok(Value::new_true()));

        let result = eval_string("case <b=false> as <a:Nat, b:Bool> of <a=x> => true | <b=y> => y".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("case <c=false> as <a:Nat, b:Bool, c:Bool> of <a=x> => true | <b=y> => y | <c=z> => z".to_string());
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
    fn test_eval_fix() {
        // 10 + x function
        let result = eval_string("
            (fix -> ie:Nat->Nat {
                -> x:Nat {
                    if iszero x
                    then 10
                    else succ (ie pred x)
                }
            } 10)
        ".to_string());
        assert_eq!(result, Ok(Value::new_nat(20)));
    }

    #[test]
    fn test_eval_unit_derived_form() {
        let result = eval_string("unit; false".to_string());
        assert_eq!(result, Ok(Value::new_false()));

        let result = eval_string("unit; unit; 2".to_string());
        assert_eq!(result, Ok(Value::new_nat(2)));
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
