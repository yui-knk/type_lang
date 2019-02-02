#[cfg(test)]
mod tests {
    lalrpop_mod!(pub parser);
    use node::{Node, Kind, Cases, Fields};
    use ty::{Ty, Kind as TyKind, Fields as TyFields};

    #[test]
    fn test_parse_nat() {
        let result = parser::ProgramParser::new().parse(" 11 ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_nat(11));
    }

    #[test]
    fn test_parse_iszero() {
        let result = parser::ProgramParser::new().parse(" iszero 10");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_iszero(Node::new_nat(10)));
    }

    #[test]
    fn test_parse_pred() {
        let result = parser::ProgramParser::new().parse(" pred 10");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_pred(Node::new_nat(10)));

        let result = parser::ProgramParser::new().parse(" pred false");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_pred(Node::new_bool(false)));
    }

    #[test]
    fn test_parse_succ() {
        let result = parser::ProgramParser::new().parse(" succ 10");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_nat(11));

        let result = parser::ProgramParser::new().parse(" succ false");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_succ(Node::new_bool(false)));
    }

    #[test]
    fn test_parse_true() {
        let result = parser::ProgramParser::new().parse(" true ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node { kind: Kind::Bool(true) });
    }

    #[test]
    fn test_parse_false() {
        let result = parser::ProgramParser::new().parse(" false ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node { kind: Kind::Bool(false) });
    }

    #[test]
    fn test_parse_true_false() {
        let result = parser::ProgramParser::new().parse(" true false ");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_as() {
        let result = parser::ProgramParser::new().parse(" false as Bool ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::As(Box::new(Node::new_bool(false)), Box::new(Ty::new_bool()))
        });

        let result = parser::ProgramParser::new().parse(" 1 as Nat ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::As(Box::new(Node::new_nat(1)), Box::new(Ty::new_nat()))
        });
    }

    #[test]
    fn test_parse_var_ref() {
        let result = parser::ProgramParser::new().parse(" x ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::VarRef("x".to_string())
        });
    }

    #[test]
    fn test_parse_lambda() {
        let result = parser::ProgramParser::new().parse("  -> x : Bool -> Bool { false } ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node
            { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_arrow(Ty::new_bool(), Ty::new_bool()))
            )}
        );
    }

    #[test]
    fn test_parse_let() {
        let result = parser::ProgramParser::new().parse(" let x = 1 in false ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node
            { kind: Kind::Let(
                "x".to_string(),
                Box::new(Node::new_nat(1)),
                Box::new(Node { kind: Kind::Bool(false) })
            )}
        );
    }

    #[test]
    fn test_parse_lambda_nested_arrow_type() {
        let result = parser::ProgramParser::new().parse(" -> x : Bool -> Bool -> Bool { false } ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node
            { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_arrow(Ty::new_bool(), Ty::new_arrow(Ty::new_bool(), Ty::new_bool())))
            )}
        );
    }

    #[test]
    fn test_parse_fix() {
        let result = parser::ProgramParser::new().parse("fix ( -> x : Bool -> Bool { false } )");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_fix(
            Node { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_arrow(Ty::new_bool(), Ty::new_bool()))
            )}
        ));

        let result = parser::ProgramParser::new().parse("fix (-> x : Bool { false })");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_fix(
            Node { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_bool())
            )}
        ));

        let result = parser::ProgramParser::new().parse("
            (fix
                (-> ie:Nat->Nat {
                    -> x:Nat {
                        if iszero x
                        then 10
                        else succ ie..(pred x)
                    }
                })
            )..(10)
        ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_apply(
            Node::new_fix(
                Node::new_lambda(
                    "ie".to_string(),
                    Node::new_lambda(
                        "x".to_string(),
                        Node::new_if(
                            Node::new_iszero(
                                Node::new_var_ref("x".to_string())
                            ),
                            Node::new_nat(10),
                            Node::new_succ(
                                Node::new_apply(
                                    Node::new_var_ref("ie".to_string()),
                                    Node::new_pred(
                                        Node::new_var_ref("x".to_string())
                                    )
                                )
                            )
                        ),
                        Ty::new_nat()
                    ),
                    Ty::new_arrow(Ty::new_nat(), Ty::new_nat())
                )
            ),
            Node::new_nat(10)
        ));
    }

    #[test]
    fn test_parse_lambda_not_arrow_type() {
        let result = parser::ProgramParser::new().parse("-> x : Bool { false }");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node
            { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node{ kind: Kind::Bool(false) }),
                Box::new(Ty::new_bool())
            )}
        );
    }

    #[test]
    fn test_parse_apply() {
        let result = parser::ProgramParser::new().parse(" x..(y) ");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Apply(
                Box::new(Node { kind: Kind::VarRef("x".to_string()) }),
                Box::new(Node { kind: Kind::VarRef("y".to_string()) })
            )}
        );
    }

    #[test]
    fn test_parse_apply_2() {
        let result = parser::ProgramParser::new().parse(" (-> x : Bool -> Bool { x })..(false) ");
        println!("{:?}", result);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Apply(
                Box::new(Node { kind: Kind::Lambda(
                    "x".to_string(),
                    Box::new(Node { kind: Kind::VarRef("x".to_string()) }),
                    Box::new(Ty::new_arrow(Ty::new_bool(), Ty::new_bool()))
                 )}),
                Box::new(Node { kind: Kind::Bool(false) })
            )}
        );
    }

    #[test]
    fn test_parse_record() {
        let result = parser::ProgramParser::new().parse(" {10, a=false, true} ");
        let mut fields = Fields::new();

        fields.insert("0".to_string(), Box::new(Node::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Node::new_bool(false)));
        fields.insert("2".to_string(), Box::new(Node::new_bool(true)));

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Record(fields)
        });
    }

    #[test]
    fn test_parse_variant_type() {
        let result = parser::TypeParser::new().parse(" <a:Bool, b:Nat> ");
        let mut fields = TyFields::new();

        fields.insert("a".to_string(), Box::new(Ty::new_bool()));
        fields.insert("b".to_string(), Box::new(Ty::new_nat()));

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Ty {
            kind: TyKind::Variant(fields)
        });
    }

    #[test]
    fn test_parse_top_type() {
        let result = parser::TypeParser::new().parse("Top");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Ty {
            kind: TyKind::Top
        });
    }

    #[test]
    fn test_parse_unit_type() {
        let result = parser::TypeParser::new().parse("Unit");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Ty {
            kind: TyKind::Unit
        });
    }

    #[test]
    fn test_parse_record_type() {
        let result = parser::TypeParser::new().parse("{a:Bool, b:Nat}");
        let mut fields = TyFields::new();

        fields.insert("a".to_string(), Box::new(Ty::new_bool()));
        fields.insert("b".to_string(), Box::new(Ty::new_nat()));

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Ty {
            kind: TyKind::Record(fields)
        });
    }

    #[test]
    fn test_parse_record_arrow_type() {
        let result = parser::TypeParser::new().parse("{a:Bool, b:Nat} -> {b:Nat}");
        let mut f1 = TyFields::new();
        let mut f2 = TyFields::new();

        f1.insert("a".to_string(), Box::new(Ty::new_bool()));
        f1.insert("b".to_string(), Box::new(Ty::new_nat()));
        f2.insert("b".to_string(), Box::new(Ty::new_nat()));

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Ty::new_arrow(Ty::new_record(f1), Ty::new_record(f2)));
    }

    #[test]
    fn test_parse_case() {
        let result = parser::ProgramParser::new().parse("case <a=1> as <a:Nat, b:Bool> of <a=x> => x | <b=y> => y");
        let mut cases = Cases::new();
        let mut ty_fields = TyFields::new();

        cases.insert("a".to_string(), "x".to_string(), Node::new_var_ref("x".to_string()));
        cases.insert("b".to_string(), "y".to_string(), Node::new_var_ref("y".to_string()));

        ty_fields.insert("a".to_string(), Box::new(Ty::new_nat()));
        ty_fields.insert("b".to_string(), Box::new(Ty::new_bool()));

        let node = Node::new_tag("a".to_string(), Node::new_nat(1), Ty::new_variant(ty_fields));

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node::new_case(node, cases));
    }

    #[test]
    fn test_parse_projection() {
        let result = parser::ProgramParser::new().parse("{10, a=false, true}.a");
        let mut fields = Fields::new();

        fields.insert("0".to_string(), Box::new(Node::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Node::new_bool(false)));
        fields.insert("2".to_string(), Box::new(Node::new_bool(true)));

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Projection(
                Box::new(Node { kind: Kind::Record(fields) }),
                "a".to_string()
            )}
        );
    }

    #[test]
    fn test_parse_projection2() {
        let result = parser::ProgramParser::new().parse("{10, a=false, true}.2");
        let mut fields = Fields::new();

        fields.insert("0".to_string(), Box::new(Node::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Node::new_bool(false)));
        fields.insert("2".to_string(), Box::new(Node::new_bool(true)));

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Projection(
                Box::new(Node { kind: Kind::Record(fields) }),
                "2".to_string()
            )}
        );
    }

    #[test]
    fn test_parse_tag1() {
        let result = parser::ProgramParser::new().parse("<bl=false> as Bool");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Tag(
                "bl".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_bool())
            )}
        );
    }

    #[test]
    fn test_parse_tag2() {
        let result = parser::ProgramParser::new().parse("<nl=1> as Nat");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Tag(
                "nl".to_string(),
                Box::new(Node::new_nat(1)),
                Box::new(Ty::new_nat())
            )}
        );
    }

    #[test]
    fn test_parse_if() {
        let result = parser::ProgramParser::new().parse("if true then false else true");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::If(
                Box::new(Node { kind: Kind::Bool(true) }),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Node { kind: Kind::Bool(true) })
            )}
        );
    }

    #[test]
    fn test_parse_ref() {
        let result = parser::ProgramParser::new().parse("ref false");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Ref(
                Box::new(Node { kind: Kind::Bool(false) }),
            )}
        );
    }

    #[test]
    fn test_parse_deref() {
        let result = parser::ProgramParser::new().parse("!false");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Deref(
                Box::new(Node { kind: Kind::Bool(false) }),
            )}
        );
    }

    #[test]
    fn test_parse_assign() {
        let result = parser::ProgramParser::new().parse("a := b");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Assign(
                Box::new(Node { kind: Kind::VarRef("a".to_string()) }),
                Box::new(Node { kind: Kind::VarRef("b".to_string()) }),
            )}
        );
    }

    #[test]
    fn test_parse_unit_derived_form() {
        let result = parser::ProgramParser::new().parse("1; false");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Node {
            kind: Kind::Apply(
                Box::new(Node { kind: Kind::Lambda(
                    "_".to_string(),
                    Box::new(Node { kind: Kind::Bool(false) }),
                    Box::new(Ty::new_unit())
                 )}),
                Box::new(Node::new_nat(1))
            )}
        );
    }
}
