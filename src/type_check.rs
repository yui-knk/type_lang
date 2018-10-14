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

    // -- SUBTYPING --

    // `subtype_eq` checks `ty1` is a sub type of `ty2`, as `ty1 <: ty2`.
    //
    // As Fig.15-1 (P.145), subtyping rules "S-*" do not
    // change the type of terms. Only "T-SUB" changes the tyep
    // of terms.
    fn subtype_eq(&self, ty1: &Ty, ty2: &Ty) -> bool {
        if self.type_eq(ty1, ty2) { return true; }

        match (&ty1.kind, &ty2.kind) {
            (TyKind::Arrow(ref ty11, ref ty12), TyKind::Arrow(ref ty21, ref ty22)) => {
                // T1 <: S1    S2 <: T2
                // --------------------
                // S1 -> S2 <: T1 -> T2
                self.subtype_eq(ty21, ty11) && self.subtype_eq(ty12, ty22)
            },
            (TyKind::Record(ref f1), TyKind::Record(ref f2)) => {
                f2.iter()
                    .all(|(s2, ty2)|
                        match f1.get(&s2) {
                            Some(ty) => self.subtype_eq(ty, ty2),
                            None => false
                        }
                    )
            },
            _ => false
        }
    }

    fn type_eq(&self, ty1: &Ty, ty2: &Ty) -> bool {
        match (&ty1.kind, &ty2.kind) {
            (TyKind::Arrow(ref ty11, ref ty12), TyKind::Arrow(ref ty21, ref ty22)) => {
                self.type_eq(ty11, ty21) && self.type_eq(ty12, ty22)
            },
            (TyKind::Bool, TyKind::Bool) => true,
            (TyKind::Nat, TyKind::Nat) => true,
            (TyKind::Record(ref f1), TyKind::Record(ref f2)) => {
                (f1.iter().len() == f2.iter().len()) &&
                f1.iter().zip(f2.iter())
                  .all(|((s1, ty1), (s2, ty2))| (s1 == s2) && self.type_eq(ty1, ty2) )
            },
            (TyKind::Variant(ref f1), TyKind::Variant(ref f2)) => {
                (f1.iter().len() == f2.iter().len()) && 
                f1.iter().zip(f2.iter())
                  .all(|((s1, ty1), (s2, ty2))| (s1 == s2) && self.type_eq(ty1, ty2) )
            },
            (TyKind::Unit, TyKind::Unit) => true,
            (TyKind::Ref(ref ty11), TyKind::Ref(ref ty21)) => self.type_eq(ty11, ty21),
            _ => false
        }
    }

    // -- TYPING --

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

                if !self.subtype_eq(&node_type, ty) {
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
            Kind::Fix(ref node) => {
                let node_type = self.type_of(node)?;

                match node_type.kind {
                    TyKind::Arrow(ty1, ty2) => {
                        if ty1 == ty2 { return Ok(*ty2); }
                        return Err(Error::TypeMismatch(format!(
                            "Domain/Result type mismatch. domain: {:?}, result: {:?}", ty1.kind, ty2.kind)));

                    },
                    _ => Err(Error::TypeMismatch(format!("{:?} is not arrow type.", node_type.kind)))
                }
            },
            Kind::Ref(ref node) => {
                let node_type = self.type_of(node)?;
                Ok(Ty::new_ref(node_type))
            },
            Kind::Deref(ref node) => {
                let node_type = self.type_of(node)?;

                match node_type.kind {
                    TyKind::Ref(ty) => {
                        Ok(*ty)
                    },
                    _ => Err(Error::TypeMismatch(format!("{:?} is not ref type.", node_type.kind)))
                }
            },
            Kind::Assign(ref left, ref right) => {
                let left_type = self.type_of(left)?;
                let right_type = self.type_of(right)?;

                match left_type.kind {
                    TyKind::Ref(ty) => {
                        if right_type == *ty { return Ok(Ty::new_unit()); }
                        return Err(Error::TypeMismatch(format!(
                            "Left/Right type mismatch. left: {:?}, right: {:?}", left.kind, right.kind)));
                    },
                    _ => Err(Error::TypeMismatch(format!("{:?} is not ref type.", left_type.kind)))
                }
            },
            Kind::Loc(..) => {
                Err(Error::TypeMismatch(format!("User can not input Loc node: {:?}.", node)))
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
mod tests_subtype_eq {
    use super::*;

    #[test]
    fn test_subtype_eq_arrow() {
        let type_checker = TypeChecker::new();

        // {a=10, b=false, c=true}
        let mut f1 = Fields::new();
        f1.insert("a".to_string(), Box::new(Ty::new_nat()));
        f1.insert("b".to_string(), Box::new(Ty::new_bool()));
        f1.insert("c".to_string(), Box::new(Ty::new_bool()));
        let r1 = Ty::new_record(f1);

        // {a=10, b=false}
        let mut f2 = Fields::new();
        f2.insert("a".to_string(), Box::new(Ty::new_nat()));
        f2.insert("b".to_string(), Box::new(Ty::new_bool()));
        let r2 = Ty::new_record(f2);

        // {b=false, c=true}
        let mut f3 = Fields::new();
        f3.insert("b".to_string(), Box::new(Ty::new_bool()));
        f3.insert("c".to_string(), Box::new(Ty::new_bool()));
        let r3 = Ty::new_record(f3);

        let arrow1 = Ty::new_arrow(r2, r1.clone());
        let arrow2 = Ty::new_arrow(r1, r3);
        let result = type_checker.subtype_eq(&arrow1, &arrow2);
        assert!(result);

        let result = type_checker.subtype_eq(&arrow2, &arrow1);
        assert!(!result);
    }

    #[test]
    fn test_subtype_eq_record() {
        let type_checker = TypeChecker::new();

        // {a=10, b=false, c=true}
        let mut f1 = Fields::new();
        f1.insert("a".to_string(), Box::new(Ty::new_nat()));
        f1.insert("b".to_string(), Box::new(Ty::new_bool()));
        f1.insert("c".to_string(), Box::new(Ty::new_bool()));
        let r1 = Ty::new_record(f1);

        // {a=10, b=false}
        let mut f2 = Fields::new();
        f2.insert("a".to_string(), Box::new(Ty::new_nat()));
        f2.insert("b".to_string(), Box::new(Ty::new_bool()));
        let r2 = Ty::new_record(f2);

        // {b=false, c=true}
        let mut f3 = Fields::new();
        f3.insert("b".to_string(), Box::new(Ty::new_bool()));
        f3.insert("c".to_string(), Box::new(Ty::new_bool()));
        let r3 = Ty::new_record(f3);

        let result = type_checker.subtype_eq(&r1, &r2);
        assert!(result);

        let result = type_checker.subtype_eq(&r1, &r3);
        assert!(result);

        let result = type_checker.subtype_eq(&r2, &r3);
        assert!(!result);
    }
}

#[cfg(test)]
mod tests_type_eq {
    use super::*;

    #[test]
    fn test_type_eq_arrow() {
        let type_checker = TypeChecker::new();
        let arrow1 = Ty::new_arrow(Ty::new_bool(), Ty::new_nat());
        let arrow2 = Ty::new_arrow(Ty::new_bool(), Ty::new_nat());
        let result = type_checker.type_eq(&arrow1, &arrow2);
        assert!(result);

        let arrow3 = Ty::new_arrow(Ty::new_nat(), Ty::new_bool());
        let arrow4 = Ty::new_arrow(Ty::new_bool(), Ty::new_nat());
        let result = type_checker.type_eq(&arrow3, &arrow4);
        assert!(!result);
    }

    #[test]
    fn test_type_eq_bool() {
        let type_checker = TypeChecker::new();
        let result = type_checker.type_eq(&Ty::new_bool(), &Ty::new_bool());
        assert!(result);

        let result = type_checker.type_eq(&Ty::new_bool(), &Ty::new_nat());
        assert!(!result);
    }

    #[test]
    fn test_type_eq_nat() {
        let type_checker = TypeChecker::new();
        let result = type_checker.type_eq(&Ty::new_nat(), &Ty::new_nat());
        assert!(result);

        let result = type_checker.type_eq(&Ty::new_nat(), &Ty::new_bool());
        assert!(!result);
    }

    #[test]
    fn test_type_eq_record() {
        let type_checker = TypeChecker::new();

        // {10, a=false, true}
        let mut f1 = Fields::new();
        f1.insert("0".to_string(), Box::new(Ty::new_nat()));
        f1.insert("a".to_string(), Box::new(Ty::new_bool()));
        f1.insert("2".to_string(), Box::new(Ty::new_bool()));
        let r1 = Ty::new_record(f1);

        // {10, a=false, true}
        let mut f2 = Fields::new();
        f2.insert("0".to_string(), Box::new(Ty::new_nat()));
        f2.insert("a".to_string(), Box::new(Ty::new_bool()));
        f2.insert("2".to_string(), Box::new(Ty::new_bool()));
        let r2 = Ty::new_record(f2);

        // {false, a=10, true}
        let mut f3 = Fields::new();
        f3.insert("0".to_string(), Box::new(Ty::new_bool()));
        f3.insert("a".to_string(), Box::new(Ty::new_nat()));
        f3.insert("2".to_string(), Box::new(Ty::new_bool()));
        let r3 = Ty::new_record(f3);

        let result = type_checker.type_eq(&r1, &r2);
        assert!(result);

        let result = type_checker.type_eq(&r1, &r3);
        assert!(!result);
    }

    #[test]
    fn test_type_eq_variant() {
        let type_checker = TypeChecker::new();

        // <a:Nat, b:Bool>
        let mut f1 = Fields::new();
        f1.insert("a".to_string(), Box::new(Ty::new_nat()));
        f1.insert("b".to_string(), Box::new(Ty::new_bool()));
        let v1 = Ty::new_record(f1);

        // <a:Nat, b:Bool>
        let mut f2 = Fields::new();
        f2.insert("a".to_string(), Box::new(Ty::new_nat()));
        f2.insert("b".to_string(), Box::new(Ty::new_bool()));
        let v2 = Ty::new_record(f2);

        // <a:Bool, b:Nat>
        let mut f3 = Fields::new();
        f3.insert("a".to_string(), Box::new(Ty::new_bool()));
        f3.insert("b".to_string(), Box::new(Ty::new_nat()));
        let v3 = Ty::new_record(f3);

        let result = type_checker.type_eq(&v1, &v2);
        assert!(result);

        let result = type_checker.type_eq(&v1, &v3);
        assert!(!result);    }

    #[test]
    fn test_type_eq_unit() {
        let type_checker = TypeChecker::new();
        let result = type_checker.type_eq(&Ty::new_unit(), &Ty::new_unit());
        assert!(result);

        let result = type_checker.type_eq(&Ty::new_unit(), &Ty::new_bool());
        assert!(!result);
    }

    #[test]
    fn test_type_eq_ref() {
        let type_checker = TypeChecker::new();
        let r1 = Ty::new_ref(Ty::new_bool());
        let r2 = Ty::new_ref(Ty::new_bool());
        let r3 = Ty::new_ref(Ty::new_nat());

        let result = type_checker.type_eq(&r1, &r2);
        assert!(result);

        let result = type_checker.type_eq(&r1, &r3);
        assert!(!result);

        let result = type_checker.type_eq(&r1, &Ty::new_bool());
        assert!(!result);
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

        // subtyping
        let mut fields = Fields::new();
        fields.insert("a".to_string(), Box::new(Ty::new_bool()));
        fields.insert("b".to_string(), Box::new(Ty::new_nat()));
        let recode_ty = Ty::new_record(fields);

        let result = check_type_of_string("{a=false, b=10} as {a:Bool}".to_string());
        assert_eq!(result, Ok(recode_ty.clone()));

        let result = check_type_of_string("{a=false, b=10} as {b:Nat}".to_string());
        assert_eq!(result, Ok(recode_ty.clone()));

        let result = check_type_of_string("{a=false} as {a:Bool, b:Nat}".to_string());
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
    fn test_check_fix() {
        let result = check_type_of_string("fix -> x : Bool { false } ".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("fix -> x : Bool -> Bool { x }".to_string());
        assert_eq!(result, Ok(Ty::new_arrow(Ty::new_bool(), Ty::new_bool())));

        let result = check_type_of_string("fix -> x : Bool -> Bool { false }".to_string());
        assert!(result.is_err());
    }

    #[test]
    fn test_check_ref() {
        let result = check_type_of_string("ref false".to_string());
        assert_eq!(result, Ok(Ty::new_ref(Ty::new_bool())));
    }

    #[test]
    fn test_check_deref() {
        let result = check_type_of_string("! ref false".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("! false".to_string());
        assert!(result.is_err());
    }

    #[test]
    fn test_check_assign() {
        let result = check_type_of_string("let x = ref false in x := true".to_string());
        assert_eq!(result, Ok(Ty::new_unit()));

        let result = check_type_of_string("ref false := 1".to_string());
        assert!(result.is_err());
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
        let result = check_type_of_string("<a=1> as <a:Nat, b:Bool>".to_string());
        let mut fields = Fields::new();
        fields.insert("a".to_string(), Box::new(Ty::new_nat()));
        fields.insert("b".to_string(), Box::new(Ty::new_bool()));
        assert_eq!(result, Ok(Ty::new_variant(fields)));

        let result = check_type_of_string("<b=false> as <a:Nat, b:Bool>".to_string());
        let mut fields = Fields::new();
        fields.insert("a".to_string(), Box::new(Ty::new_nat()));
        fields.insert("b".to_string(), Box::new(Ty::new_bool()));
        assert_eq!(result, Ok(Ty::new_variant(fields)));

        let result = check_type_of_string("<a=false> as <a:Nat, b:Bool>".to_string());
        assert!(result.is_err());

        let result = check_type_of_string("<b=1> as <a:Nat, b:Bool>".to_string());
        assert!(result.is_err());
    }

    #[test]
    fn test_check_case() {
        let result = check_type_of_string("case <a=1>     as <a:Nat, b:Bool> of <a=x> => x | <b=y> => 2".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));

        let result = check_type_of_string("case <b=false> as <a:Nat, b:Bool> of <a=x> => x | <b=y> => 2".to_string());
        assert_eq!(result, Ok(Ty::new_nat()));

        let result = check_type_of_string("case <a=1>     as <a:Nat, b:Bool> of <a=x> => true | <b=y> => y".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("case <b=false> as <a:Nat, b:Bool> of <a=x> => true | <b=y> => y".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("case <a=1> as <a:Nat, b:Bool> of <a=x> => x | <b=y> => y".to_string());
        assert!(result.is_err());

        let result = check_type_of_string("case <c=false> as <a:Nat, b:Bool> of <a=x> => true | <b=y> => y".to_string());
        assert!(result.is_err());

        let result = check_type_of_string("case <b=false> as <a:Nat, b:Bool> of <a=x> => true | <c=y> => y".to_string());
        assert!(result.is_err());

        let result = check_type_of_string("case <b=false> as <a:Nat, b:Bool, c:Bool> of <a=x> => true | <c=y> => y".to_string());
        assert!(result.is_err());

        let result = check_type_of_string("case <b=false> as <a:Nat, b:Bool> of <a=x> => true | <b=y> => y | <c=z> => z".to_string());
        assert!(result.is_err());
    }

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
