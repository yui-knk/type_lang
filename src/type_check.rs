use node::{Node, Kind};
use ty::{Ty, Kind as TyKind};

#[derive(Debug, PartialEq)]
struct Context {
    // Mapping from variable to value.
    // Use Vec as a stack.
    //
    // Value may be shared multi lambda bodies.
   stack: Vec<(String, Ty)>    
}

#[derive(Debug, PartialEq)]
struct VarGen {
    id: usize
}

#[derive(Debug, PartialEq)]
pub struct TypeChecker {
    context: Context,
    vargen: VarGen,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    TypeMismatch(String),
    VariableNotFound(String),
    IndexError(String),
    CircularConstraints(String),
    UnsolvableConstraints(Ty, Ty),
    UnexpectedConstraints(Ty, Ty),
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

impl VarGen {
    fn new() -> VarGen {
        VarGen { id: 0 }
    }

    fn next_id(&mut self) -> String {
        let s = format!{"Var{}", self.id};
        self.id += 1;
        s
    }
}

type Constraints = Vec<(Ty, Ty)>;

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker { context: Context::new(), vargen: VarGen::new() }
    }

    pub fn check(&mut self, node: &Node) -> Result<Ty, Error> {
        let (ty, constr1) = self.recon(&node)?;
        let constr2 = self.unify(constr1)?;
        self.applysubst(ty, constr2)
    }

    #[allow(dead_code)]
    fn type_eq(&self, ty1: &Ty, ty2: &Ty) -> bool {
        match (&ty1.kind, &ty2.kind) {
            (TyKind::Arrow(ref ty11, ref ty12), TyKind::Arrow(ref ty21, ref ty22)) => {
                self.type_eq(ty11, ty21) && self.type_eq(ty12, ty22)
            },
            (TyKind::Bool, TyKind::Bool) => true,
            (TyKind::Nat, TyKind::Nat) => true,
            _ => false
        }
    }

    // -- TYPE reconstruction --

    fn recon(&mut self, node: &Node) -> Result<(Ty, Constraints), Error> {
        match node.kind {
            Kind::NoneExpression => {
                // We do not have unit-type now
                Ok((Ty::new_bool(), Vec::new()))
            },
            Kind::VarRef(ref var) => {
                match self.context.find_by_variable(var) {
                    Some(ty) => Ok((ty, Vec::new())),
                    None => Err(Error::VariableNotFound(var.clone()))
                }
            },
            Kind::Lambda(ref var, ref body, ref ty_opt) => {
                match **ty_opt {
                    Some(ref ty) => {
                        self.context.push(var.clone(), ty.clone());
                        let (body_ty, constr2) = self.recon(body)?;
                        self.context.pop();
                        Ok((Ty::new_arrow(ty.clone(), body_ty), constr2))
                    },
                    None => {
                        let ty = Ty::new_id(self.vargen.next_id());
                        self.context.push(var.clone(), ty.clone());
                        let (body_ty, constr2) = self.recon(body)?;
                        self.context.pop();
                        Ok((Ty::new_arrow(ty.clone(), body_ty), constr2))
                    }
                }
            },
            Kind::Apply(ref rec, ref arg) => {
                // t1 : T1   t2: T2
                // ----------------
                // t1 t2 : X  {t1 = t2 -> X}
                let (rec_type, mut constr1) = self.recon(rec)?;
                let (arg_type, mut constr2) = self.recon(arg)?;
                let id = self.vargen.next_id();
                let mut new_constr = vec!((rec_type, Ty::new_arrow(arg_type, Ty::new_id(id.clone()))));
                new_constr.append(&mut constr1);
                new_constr.append(&mut constr2);
                Ok((Ty::new_id(id), new_constr))
            },
            Kind::Let(ref var, ref bound, ref body) => {
                let (bound_ty, mut constr1) = self.recon(bound)?;
                self.context.push(var.clone(), bound_ty);
                let (body_ty, mut constr2) = self.recon(body)?;
                self.context.pop();
                constr1.append(&mut constr2);
                Ok((body_ty, constr1))
            },
            Kind::Bool(_) => Ok((Ty::new_bool(), Vec::new())),
            Kind::Zero => Ok((Ty::new_nat(), Vec::new())),
            Kind::Succ(ref operand) => {
                let (operand_type, mut constr1) = self.recon(operand)?;
                constr1.push((Ty::new_nat(), operand_type));
                Ok((Ty::new_nat(), constr1))
            },
            Kind::Pred(ref operand) => {
                let (operand_type, mut constr1) = self.recon(operand)?;
                constr1.push((Ty::new_nat(), operand_type));
                Ok((Ty::new_nat(), constr1))
            },
            Kind::Iszero(ref operand) => {
                let (operand_type, mut constr1) = self.recon(operand)?;
                constr1.push((Ty::new_nat(), operand_type));
                Ok((Ty::new_bool(), constr1))
            },
            Kind::If(ref cond, ref then_expr, ref else_expr) => {
                let (cond_type, mut constr1) = self.recon(cond)?;
                let (then_type, mut constr2) = self.recon(then_expr)?;
                let (else_type, mut constr3) = self.recon(else_expr)?;
                let mut constr = vec![(cond_type, Ty::new_bool()), (then_type.clone(), else_type.clone())];
                constr.append(&mut constr1);
                constr.append(&mut constr2);
                constr.append(&mut constr3);
                Ok((then_type, constr))
            },
        }
    }

    fn applysubst(&self, mut ty: Ty, constr: Constraints) -> Result<Ty, Error> {
        // I'm not clear why fold with reverse order...
        for (t1, t2) in constr.into_iter().rev() {
            match t1.clone().kind {
                // All left values of "unify" function's result should be Id Ty.
                TyKind::Id(s) => {
                    ty = self.replace_constr(&s, &t2, ty)
                },
                _ => { return Err(Error::UnexpectedConstraints(t1, t2)); }
            }
        }

        Ok(ty)
    }

    fn occursin(&self, id: &String, ty: &Ty) -> bool {
        match ty.kind {
            TyKind::Arrow(ref l, ref r) => self.occursin(id, &*l) || self.occursin(id, &*r),
            TyKind::Bool => false,
            TyKind::Nat => false,
            TyKind::Id(ref s) => s == id
        }
    }

    fn replace_constr(&self, id: &String, ty: &Ty, ty1: Ty) -> Ty {
        match ty1.clone().kind {
            TyKind::Arrow(l, r) => Ty::new_arrow(self.replace_constr(id, ty, *l), self.replace_constr(id, ty, *r)),
            TyKind::Bool => ty1,
            TyKind::Nat => ty1,
            TyKind::Id(s) => {
                if s == *id {
                    ty.clone()
                } else {
                    ty1
                }
            }
        }
    }

    // This function replace type variable whose id is equal to "id" argument
    // with "ty" type.
    fn replace_constrs(&self, id: &String, ty: &Ty, constr: Constraints) -> Constraints {
        constr.into_iter().map(|(t1, t2)| (self.replace_constr(id, ty, t1), self.replace_constr(id, ty, t2))).collect()
    }

    // This function gets type constraints and returns an assignment.
    // All left values of returned constraints are Id Ty.
    fn unify(&mut self, mut constr: Constraints) -> Result<Constraints, Error> {
        if constr.len() == 0 { return Ok(Vec::new()); }

        let (t1, t2) = constr.pop().unwrap();
        match (t1.clone().kind, t2.clone().kind) {
            (t, TyKind::Id(id)) => {
                // Same type variable
                if t == TyKind::Id(id.clone()) { return self.unify(constr); }
                if self.occursin(&id, &t1) { return Err(Error::CircularConstraints(id.clone())) };
                constr = self.replace_constrs(&id, &t1, constr);
                let mut result = self.unify(constr)?;
                // t1 is assigned to a type variable.
                result.push((Ty::new_id(id), t1));
                Ok(result)
            },
            (TyKind::Id(id), t) => {
                // Same type variable
                if t == TyKind::Id(id.clone()) { return self.unify(constr); }
                if self.occursin(&id, &t2) { return Err(Error::CircularConstraints(id.clone())) };
                constr = self.replace_constrs(&id, &t2, constr);;
                let mut result = self.unify(constr)?;
                // t2 is assigned to a type variable.
                result.push((Ty::new_id(id), t2));
                Ok(result)
            },
            (TyKind::Bool, TyKind::Bool) => {
                self.unify(constr)
            },
            (TyKind::Nat, TyKind::Nat) => {
                self.unify(constr)
            },
            (TyKind::Arrow(t11, t12), TyKind::Arrow(t21, t22)) => {
                constr.push((*t11, *t21));
                constr.push((*t12, *t22));
                self.unify(constr)
            },
            _ => Err(Error::UnsolvableConstraints(t1, t2))
        }
    }

    // -- TYPING --

    #[allow(dead_code)]
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
            Kind::Lambda(ref var, ref body, ref ty_opt) => {
                let ty : &Ty = ty_opt.as_ref().as_ref().expect("Type should be resolved here.");
                self.context.push(var.clone(), ty.clone());
                let body_ty = self.type_of(body)?;
                self.context.pop();
                Ok(Ty::new_arrow(ty.clone(), body_ty))
            },
            Kind::Apply(ref rec, ref arg) => {
                let rec_type = self.type_of(rec)?;
                let arg_type = self.type_of(arg)?;

                match rec_type.kind {
                    TyKind::Arrow(ty1, ty2) => {
                        if self.type_eq(&arg_type, &*ty1) { return Ok(*ty2); }
                        return Err(Error::TypeMismatch(format!(
                            "Argument type mismatch. expected: {:?}, actual: {:?}", ty1.kind, arg_type.kind)));
                    },
                    _ => Err(Error::TypeMismatch(format!("{:?} is not arrow type.", rec_type.kind)))
                }
            },
            Kind::Bool(_) => Ok(Ty::new_bool()),
            Kind::Zero => Ok(Ty::new_nat()),
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
mod tests_vargen {
    use super::*;

    #[test]
    fn test_vargen() {
        let mut vargen = VarGen::new();

        assert_eq!(vargen.next_id(), "Var0".to_string());
        assert_eq!(vargen.next_id(), "Var1".to_string());
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
}

#[cfg(test)]
mod tests_unify {
    use super::*;
    use parser::{Parser};

    fn unify_string(str: String) -> Result<Constraints, Error> {
        let mut parser = Parser::new(str);
        let node = parser.parse().unwrap();
        let mut type_checker = TypeChecker::new();
        let (_ty, constr) = type_checker.recon(&node)?;
        type_checker.unify(constr)
    }

    #[test]
    fn test_unify_lambda() {
        let result = unify_string(" -> x : Bool { false } ".to_string());
        assert_eq!(result, Ok(
            Vec::new()
        ));

        let result = unify_string(" -> x { x } ".to_string());
        assert_eq!(result, Ok(
            Vec::new()
        ));

        let result = unify_string(" -> x { false } ".to_string());
        assert_eq!(result, Ok(
            Vec::new()
        ));

        let result = unify_string(" -> x { x.(1) } ".to_string());
        assert_eq!(result, Ok(
            vec![
                (Ty::new_id("Var0".to_string()), Ty::new_arrow(Ty::new_nat(), Ty::new_id("Var1".to_string())))
            ]
        ));

        let result = unify_string(" -> x { x.(1).(false) } ".to_string());
        assert_eq!(result, Ok(
            vec![
                (Ty::new_id("Var1".to_string()), Ty::new_arrow(Ty::new_bool(), Ty::new_id("Var2".to_string()))),
                (Ty::new_id("Var0".to_string()), Ty::new_arrow(Ty::new_nat(), Ty::new_id("Var1".to_string()))),
            ]
        ));

        let result = unify_string(" -> x { iszero x.(1) } ".to_string());
        assert_eq!(result, Ok(
            vec![
                (Ty::new_id("Var0".to_string()), Ty::new_arrow(Ty::new_nat(), Ty::new_nat())),
                (Ty::new_id("Var1".to_string()), Ty::new_nat()),
            ]
        ));
    }
}

#[cfg(test)]
mod tests_recon {
    use super::*;
    use parser::{Parser};

    fn recon_string(str: String) -> Result<(Ty, Constraints), Error> {
        let mut parser = Parser::new(str);
        let node = parser.parse().unwrap();
        let mut type_checker = TypeChecker::new();
        type_checker.recon(&node)
    }

    #[test]
    fn test_recon_lambda() {
        let result = recon_string(" -> x : Bool { false } ".to_string());
        assert_eq!(result, Ok((Ty::new_arrow(Ty::new_bool(), Ty::new_bool()), Vec::new())));

        let result = recon_string(" -> x { x } ".to_string());
        assert_eq!(result, Ok((
            Ty::new_arrow(Ty::new_id("Var0".to_string()), Ty::new_id("Var0".to_string())),
            Vec::new()
        )));

        let result = recon_string(" -> x { false } ".to_string());
        assert_eq!(result, Ok((
            Ty::new_arrow(Ty::new_id("Var0".to_string()), Ty::new_bool()),
            Vec::new()
        )));

        let result = recon_string(" -> x { x.(1) } ".to_string());
        assert_eq!(result, Ok((
            Ty::new_arrow(Ty::new_id("Var0".to_string()), Ty::new_id("Var1".to_string())),
            vec![
                (Ty::new_id("Var0".to_string()), Ty::new_arrow(Ty::new_nat(), Ty::new_id("Var1".to_string()))),
                (Ty::new_nat(), Ty::new_nat())
            ]
        )));

        let result = recon_string(" -> x { x.(1).(false) } ".to_string());
        assert_eq!(result, Ok((
            Ty::new_arrow(Ty::new_id("Var0".to_string()), Ty::new_id("Var2".to_string())),
            vec![
                (Ty::new_id("Var1".to_string()), Ty::new_arrow(Ty::new_bool(), Ty::new_id("Var2".to_string()))),
                (Ty::new_id("Var0".to_string()), Ty::new_arrow(Ty::new_nat(), Ty::new_id("Var1".to_string()))),
                (Ty::new_nat(), Ty::new_nat())
            ]
        )));

        let result = recon_string(" -> x { iszero x.(1) } ".to_string());
        assert_eq!(result, Ok((
            Ty::new_arrow(Ty::new_id("Var0".to_string()), Ty::new_bool()),
            vec![
                (Ty::new_id("Var0".to_string()), Ty::new_arrow(Ty::new_nat(), Ty::new_id("Var1".to_string()))),
                (Ty::new_nat(), Ty::new_nat()),
                (Ty::new_nat(), Ty::new_id("Var1".to_string())),
            ]
        )));

        let result = recon_string("-> x : Bool -> Bool { -> x : Bool -> Bool { x }.(x) }".to_string());
        assert_eq!(result, Ok((
            Ty::new_arrow(
                Ty::new_arrow(Ty::new_bool(), Ty::new_bool()),
                Ty::new_id("Var0".to_string())
            ),
            vec![
                (
                    Ty::new_arrow(
                        Ty::new_arrow(Ty::new_bool(), Ty::new_bool()),
                        Ty::new_arrow(Ty::new_bool(), Ty::new_bool())
                    ),
                    Ty::new_arrow(
                        Ty::new_arrow(Ty::new_bool(), Ty::new_bool()),
                        Ty::new_id("Var0".to_string())
                    ),
                )
            ]
        )));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::{Parser};

    fn check_type_of_string(str: String) -> Result<Ty, Error> {
        let mut parser = Parser::new(str);
        let node = parser.parse().unwrap();
        let mut type_checker = TypeChecker::new();
        type_checker.check(&node)
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
    fn test_check_apply() {
        let result = check_type_of_string(" -> x : Bool { false }.(true)".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("  -> x : Bool { x }.(true)".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("-> x : Bool -> Bool { x }.(-> y : Bool { false })".to_string());
        assert_eq!(result, Ok(Ty::new_arrow(Ty::new_bool(), Ty::new_bool())));

        let result = check_type_of_string("-> x : Bool -> Bool { -> x : Bool -> Bool { x }.(x) }".to_string());
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
        let result = check_type_of_string("-> x : Bool -> Bool { y }.(false)".to_string());
        assert_eq!(result, Err(Error::VariableNotFound("y".to_string())));
    }

    #[test]
    fn test_check_type_mismatch() {
        let result = check_type_of_string("false.(true)".to_string());
        assert_eq!(result, Err(Error::UnsolvableConstraints(
            Ty::new_bool(),
            Ty::new_arrow(Ty::new_bool(), Ty::new_id("Var0".to_string()))
        )));
    }

    #[test]
    fn test_check_type_variable() {
        let result = check_type_of_string("
            (-> x { x.(1) }).(
                -> y { iszero y }
            )
        ".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));
    }
}
