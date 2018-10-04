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
pub struct TypeChecker {
    context: Context
}

#[derive(Debug, PartialEq)]
pub enum Error {
    TypeMismatch(String),
    VariableNotFound(String)
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
        }
    }
}

#[cfg(test)]
mod tests_env {
    use super::*;
    use ty::Ty;

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
    use ty::Ty;

    fn check_type_of_string(str: String) -> Result<Ty, Error> {
        let mut parser = Parser::new(str);
        let node = parser.parse().unwrap();
        let mut type_checker = TypeChecker::new();
        type_checker.check(&node)
    }

    #[test]
    fn test_check_bool() {
        let result = check_type_of_string("false".to_string());
        assert_eq!(result, Ok(Ty::new_bool()));

        let result = check_type_of_string("true".to_string());
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
