use itertools::Itertools;

use node::{Node, Kind};
use ty::{Ty, Kind as TyKind, Fields};

#[derive(Debug, PartialEq)]
struct Context {
    // Mapping from variable to value.
    // Use Vec as a stack.
    //
    // Value may be shared multi lambda bodies.
   stack: Vec<(String, Ty)>    
}

#[derive(Debug, PartialEq)]
pub struct TypeChecker {
    context: Context
}

#[derive(Debug, PartialEq)]
pub enum Error {
    TypeMismatch(String),
    VariableNotFound(String),
    IndexError(String)
}

impl Context {
    fn new() -> Context {
        Context { stack: Vec::new() }
    }

    fn push(&mut self, variable: String, ty: Ty) {
        self.stack.push((variable, ty));
    }

    fn pop(&mut self) {
        if self.stack.pop().is_none() {
            eprintln!("empty stack is popped.");
        }
    }

    fn find_by_variable(&self, variable: &str) -> Option<Ty> {
        for (str, ty) in self.stack.iter().rev() {
            if str == variable {
                return Some(ty.clone());
            }
        }

        None
    }
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker { context: Context::new() }
    }

    pub fn check(&mut self, node: &Node) -> Result<Ty, Error> {
        self.type_of(node)
    }

    fn type_of(&mut self, node: &Node) -> Result<Ty, Error> {
        match node.kind {
            Kind::NoneExpression => Ok(Ty::new_bool()), // We do not have unit-type now
            Kind::VarRef(ref var) =>{
                match self.context.find_by_variable(var) {
                    Some(ty) => Ok(ty),
                    None => Err(Error::VariableNotFound(var.clone()))
                }
            },
            Kind::Let(ref var, ref bound, ref body) => {
                let bound_ty = self.type_of(bound)?;
                self.context.push(var.clone(), bound_ty);
                let body_ty = self.type_of(body)?;
                self.context.pop();
                Ok(body_ty)
            },
            // Calculate type of body with var is bound to ty and
            // concat the result with ty as arrow type.
            Kind::Lambda(ref var, ref body, ref ty) => {
                self.context.push(var.clone(), *ty.clone());
                let body_ty = self.type_of(body)?;
                self.context.pop();
                Ok(Ty::new_arrow(*ty.clone(), body_ty))
            },
            Kind::Apply(ref rec, ref arg) => {
                let rec_type = self.type_of(rec)?;
                let arg_type = self.type_of(arg)?;

                match rec_type.kind {
                    TyKind::Arrow(ty1, ty2) => {
                        if *ty1 == arg_type { return Ok(*ty2); }
                        return Err(Error::TypeMismatch(format!(
                            "Argument type mismatch. expected: {:?}, actual: {:?}", ty1.kind, arg_type.kind)));
                    },
                    _ => Err(Error::TypeMismatch(format!("{:?} is not arrow type.", rec_type.kind)))
                }
            },
            Kind::Bool(_) => Ok(Ty::new_bool()),
            Kind::Zero => Ok(Ty::new_nat()),
            Kind::Unit => Ok(Ty::new_unit()),
            Kind::Succ(ref operand) => {
                let operand_type = self.type_of(operand)?;
                if operand_type.kind != TyKind::Nat {
                    return Err(Error::TypeMismatch(format!(
                        "Condition type mismatch. {:?} is not Nat.", operand_type.kind)));
                };

                Ok(Ty::new_nat())
            },
            Kind::Pred(ref operand) => {
                let operand_type = self.type_of(operand)?;
                if operand_type.kind != TyKind::Nat {
                    return Err(Error::TypeMismatch(format!(
                        "Condition type mismatch. {:?} is not Nat.", operand_type.kind)));
                };

                Ok(Ty::new_nat())
            },
            Kind::Iszero(ref operand) => {
                let operand_type = self.type_of(operand)?;
                if operand_type.kind != TyKind::Nat {
                    return Err(Error::TypeMismatch(format!(
                        "Condition type mismatch. {:?} is not Nat.", operand_type.kind)));
                };

                Ok(Ty::new_bool())
            },
            Kind::If(ref cond, ref then_expr, ref else_expr) => {
                // cond should be Bool and then/else should have same type
                let cond_type = self.type_of(cond)?;
                if cond_type.kind != TyKind::Bool {
                    return Err(Error::TypeMismatch(format!(
                        "Condition type mismatch. {:?} is not Bool.", cond_type.kind)));
                }
                let then_type = self.type_of(then_expr)?;
                let else_type = self.type_of(else_expr)?;

                if then_type.kind != else_type.kind {
                    return Err(Error::TypeMismatch(format!(
                        "Type mismatch. THEN: {:?}, ELSE: {:?}.", then_type.kind, else_type.kind)));
                }

                Ok(then_type)
            },
            Kind::Record(ref fields) => {
                let mut fields_type = Fields::new();

                for (s, node) in fields.iter() {
                    let node_type = self.type_of(node)?;
                    fields_type.insert(s.clone(), Box::new(node_type));
                }

                Ok(Ty::new_record(fields_type))
            },
            Kind::Projection(ref node, ref label) => {
                match node.kind {
                    Kind::Record(ref recode) => {
                        let value = recode.get(label);

                        // Maybe this includes semantic analysis
                        match value {
                            Some(value_node) => {
                                self.type_of(value_node)
                            },
                            None => Err(Error::IndexError(format!(
                                            "{} is not valid index.", label)))
                        }
                    },
                    _ => {
                        Err(Error::TypeMismatch(format!(
                            "Record type mismatch. {:?} is not Record.", node.kind)))
                    }
                }
            },
            Kind::As(ref node, ref ty) => {
                let node_type = self.type_of(node)?;

                if node_type.kind != ty.kind {
                    return Err(Error::TypeMismatch(format!(
                        "Type mismatch. EXPRESSION: {:?}, AS: {:?}.", node_type.kind, ty.kind)));
                }

                Ok(node_type)
            },
            Kind::Tag(ref tag, ref node, ref ty) => {
                // Get type from ty (should be Variant type) with tag as a key.
                // And check the type of tag to match with the type of node.

                match ty.kind {
                    TyKind::Variant(ref fields) => {
                        let node_type = self.type_of(node)?;
                        let tag_type_op = fields.get(tag);

                        match tag_type_op {
                            Some(tag_type) => {
                                if node_type != **tag_type {
                                    return Err(Error::TypeMismatch(format!(
                                        "Type mismatch. TAG: {:?}, NODE: {:?}.", tag_type, node_type)));
                                }

                                Ok(*ty.clone())
                            },
                            None => Err(Error::IndexError(format!(
                                            "{} is not valid index.", tag)))
                        }

                    },
                    _ => {
                        Err(Error::TypeMismatch(format!(
                            "Tag type mismatch. {:?} is not Variant.", ty.kind)))
                    }
                }
            },
            Kind::Case(ref variant, ref cases) => {
                // Check:
                //   (1) Type of variant node is Variant.
                //   (2) Variant type and cases has same number of labels.
                //   (3) All type of case nodes are same under the condition of
                //       a type of variant having same label with label of case is bound.

                let variant_type = self.type_of(variant)?;

                match variant_type.kind {
                    // Check (1)
                    TyKind::Variant(ref fields) => {
                        // Check (2)
                        if fields.iter().count() != cases.iter().count() {
                            return Err(Error::TypeMismatch(format!(
                                "Fields count mismatch. fields count {}, cases count {}.", fields.iter().count(), cases.iter().count())));
                        }

                        // Vec of (label, case_type)
                        let mut results = Vec::new();

                        for (label, ty) in fields.iter() {
                            let case_node_opt = cases.get(label);

                            match case_node_opt {
                                Some((var, case_node)) => {
                                    self.context.push(var.clone(), *ty.clone());
                                    let case_type = self.type_of(case_node)?;
                                    results.push((label.clone(), case_type));
                                    self.context.pop();
                                },
                                None => {
                                    return Err(Error::IndexError(format!("{} is not valid index.", label)))
                                }
                            }
                        }

                        // Check (3)
                        if results.iter().map(|(_, t)| t)
                                  .unique().count() != 1 {
                            return Err(Error::TypeMismatch(format!(
                                "Results type is not unique. results: {:?}.", results)));
                        }

                        Ok(results.first().unwrap().1.clone())
                    },
                    _ => {
                        Err(Error::TypeMismatch(format!(
                            "Tag type mismatch. {:?} is not Variant.", variant_type.kind)))
                    }
                }
            },
            // _ => panic!("")
        }
    }
}

#[cfg(test)]
mod tests_env {
    use super::*;

    #[test]
    fn test_find_by_variable() {
        let mut context = Context::new();
        let bool_ty = Ty::new_bool();
        let arrow_ty = Ty::new_arrow(Ty::new_bool(), Ty::new_bool());

        context.push("x".to_string(), bool_ty.clone());

        assert_eq!(context.find_by_variable(&"y".to_string()), None);
        assert_eq!(context.find_by_variable(&"x".to_string()), Some(bool_ty.clone()));

        context.push("y".to_string(), arrow_ty.clone());
        assert_eq!(context.find_by_variable(&"y".to_string()), Some(arrow_ty.clone()));
        assert_eq!(context.find_by_variable(&"x".to_string()), Some(bool_ty.clone()));

        context.pop();
        context.push("x".to_string(), arrow_ty.clone());
        assert_eq!(context.find_by_variable(&"y".to_string()), None);
        assert_eq!(context.find_by_variable(&"x".to_string()), Some(arrow_ty.clone()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::{Parser};
    use ty::{Fields};

    fn check_type_of_string(str: String) -> Result<Ty, Error> {
        let mut parser = Parser::new(str);
        let node = parser.parse().unwrap();
        let mut type_checker = TypeChecker::new();
        type_checker.check(&node)
    }

    #[test]
    fn test_check_unit() {
        let result = check_type_of_string("unit".to_string());
        assert_eq!(result, Ok(Ty::new_unit()));
    }

    #[test]
    fn test_check_nat() {
        let result = check_type_of_string("10".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));
    }

    #[test]
    fn test_check_bool() {
        let result = check_type_of_string("false".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("true".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));
    }

    #[test]
    fn test_check_iszero() {
        let result = check_type_of_string("iszero 10".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("iszero false".to_string());
        assert!(result.is_err());
    }

    #[test]
    fn test_check_succ() {
        let result = check_type_of_string("succ 10".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));

        let result = check_type_of_string("succ false".to_string());
        assert!(result.is_err());
    }

    #[test]
    fn test_check_pred() {
        let result = check_type_of_string("pred 10".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));

        let result = check_type_of_string("pred false".to_string());
        assert!(result.is_err());
    }

    #[test]
    fn test_check_as() {
        let result = check_type_of_string("false as Bool".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("1 as Nat".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));

        let result = check_type_of_string("1 as Bool".to_string());
        assert!(result.is_err());

        let result = check_type_of_string("false as Nat".to_string());
        assert!(result.is_err());
    }

    #[test]
    fn test_check_let() {
        let result = check_type_of_string(" let x = 1 in x ".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));

        let result = check_type_of_string(" let x = 1 in iszero x ".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string(" let x = 1 in false ".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));
    }

    #[test]
    fn test_check_lambda() {
        let result = check_type_of_string(" -> x : Bool { false } ".to_string());
        assert_eq!(result, Ok(Ty::new_arrow(Ty::new_bool(), Ty::new_bool())));

        let result = check_type_of_string("-> x : Bool -> Bool { x }".to_string());
        assert_eq!(result, Ok(Ty::new_arrow(
            Ty::new_arrow(Ty::new_bool(), Ty::new_bool()),
            Ty::new_arrow(Ty::new_bool(), Ty::new_bool())
        )));
    }

    #[test]
    fn test_check_record() {
        let result = check_type_of_string(" {10, a=false, true} ".to_string());
        let mut fields_type = Fields::new();

        fields_type.insert("0".to_string(), Box::new(Ty::new_nat()));
        fields_type.insert("a".to_string(), Box::new(Ty::new_bool()));
        fields_type.insert("2".to_string(), Box::new(Ty::new_bool()));

        assert_eq!(result, Ok(Ty::new_record(fields_type)));
    }

    #[test]
    fn test_check_projection() {
        let result = check_type_of_string(" {10, a=false, true}.0 ".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));

        let result = check_type_of_string(" {10, a=false, true}.a ".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string(" {10, a=false, true}.1 ".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string(" {10, a=false, true}.3 ".to_string());
        assert_eq!(result, Err(Error::IndexError("3 is not valid index.".to_string())));

        let result = check_type_of_string(" {10, a=false, true}.b ".to_string());
        assert_eq!(result, Err(Error::IndexError("b is not valid index.".to_string())));
    }

    #[test]
    fn test_check_variant() {
        let result = check_type_of_string("inl 1 as <Nat, Bool>".to_string());
        let mut fields = Fields::new();
        fields.insert("inl".to_string(), Box::new(Ty::new_nat()));
        fields.insert("inr".to_string(), Box::new(Ty::new_bool()));
        assert_eq!(result, Ok(Ty::new_variant(fields)));

        let result = check_type_of_string("inr false as <Nat, Bool>".to_string());
        let mut fields = Fields::new();
        fields.insert("inl".to_string(), Box::new(Ty::new_nat()));
        fields.insert("inr".to_string(), Box::new(Ty::new_bool()));
        assert_eq!(result, Ok(Ty::new_variant(fields)));

        let result = check_type_of_string("inl false as <Nat, Bool>".to_string());
        assert!(result.is_err());

        let result = check_type_of_string("inr 1 as <Nat, Bool>".to_string());
        assert!(result.is_err());
    }

    #[test]
    // fn test_check_case() {
    //     let result = check_type_of_string("case inl 1 as <Nat, Bool> of inl x => x | inr y => y".to_string());
    //     assert_eq!(result, Ok(Ty::new_nat()));
    // }

    #[test]
    fn test_check_apply() {
        let result = check_type_of_string(" (-> x : Bool { false } true)".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string(" ( -> x : Bool { x } true )".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("(-> x : Bool -> Bool{ x } -> y : Bool { false } )".to_string());
        assert_eq!(result, Ok(Ty::new_arrow(Ty::new_bool(), Ty::new_bool())));

        let result = check_type_of_string("-> x : Bool -> Bool { (-> x : Bool -> Bool { x } x) }".to_string());
        assert_eq!(result, Ok(Ty::new_arrow(
            Ty::new_arrow(Ty::new_bool(), Ty::new_bool()),
            Ty::new_arrow(Ty::new_bool(), Ty::new_bool())
        )));
    }

    #[test]
    fn test_check_if_then_else() {
        let result = check_type_of_string(" if true then false else true".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string(" if true then 10 else 11".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));

        let result = check_type_of_string(" if true then -> x : Bool { x } else true".to_string());
        assert!(result.is_err());

        let result = check_type_of_string(" if true then 10 else false".to_string());
        assert!(result.is_err());

        let result = check_type_of_string(" if 1 then 10 else 11".to_string());
        assert!(result.is_err());
    }

    #[test]
    fn test_check_variable_not_found() {
        let result = check_type_of_string("(-> x : Bool -> Bool { y } false)".to_string());
        assert_eq!(result, Err(Error::VariableNotFound("y".to_string())));
    }

    #[test]
    fn test_check_type_mismatch() {
        let result = check_type_of_string("(false true)".to_string());
        assert_eq!(result, Err(Error::TypeMismatch("Bool is not arrow type.".to_string())));
    }
}
