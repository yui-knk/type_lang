use lexer;
use node::{Node, Cases};
use token::{Kind, Keyword, Token};
use ty::{Ty, Fields};

#[derive(Debug)]
pub struct Parser {
    lexer: lexer::Lexer,
    // Buffer for once read tokens.
    // Use Vec as a stack.
    buf: Vec<Token>
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnknownToken,
    UnexpectedToken(String, Token), // expected, actual
    UnexpectedEOF,
    NotSupported(Token),
}


impl Parser {
    pub fn new(source: String) -> Parser {
        Parser {
            lexer: lexer::Lexer::new(source),
            buf: Vec::new()
        }
    }

    pub fn parse(&mut self) -> Result<Node, Error> {
        self.parse_program()
    }

    fn parse_program(&mut self) -> Result<Node, Error> {
        let node = self.parse_expressions()?;

        self.expect_eof()?;
        Ok(node)
    }

    fn parse_expressions(&mut self) -> Result<Node, Error> {
        let mut node = self.parse_expression()?;

        if node.is_none_expression() {
            return Ok(node);
        };

        let mut token = self.next_token()?;

        while token.has_keyword(&Keyword::SEMICOLON) {
            let node2 = self.parse_expression()?;
            // This is for derived form of sequencing.
            //
            //   "expr1; expr2" is "(-> _: Unit { t2 } t1)"
            //
            // Variable name should not be a free variable of t2.
            // "_" is not identifier in our lexer, so "_" is not a free variable of t2.
            node = Node::new_apply(
                Node::new_lambda("_".to_string(), node2, Ty::new_unit()),
                node
            );

            // Next token of field should be ";" or EOF, so
            // we can call next_token method here.
            token = self.next_token()?;
        }
        //
        self.unget_token(token);

        Ok(node)
    }

    fn parse_expression(&mut self) -> Result<Node, Error> {
        let mut token = self.next_token()?;

        let mut node = if token.has_keyword(&Keyword::LPAREN) {
            // "(" expr ")"
            let expr = self._parse_expression()?;
            self.expect_keyword(Keyword::RPAREN)?;
            expr
        } else {
            self.unget_token(token);
            self._parse_expression()?
        };

        token = self.next_token()?;

        if token.has_keyword(&Keyword::DOT) {
            token = self.next_token()?;

            match token.kind {
                // [apply]
                //
                // expr "." "(" expr ")" ("." "(" expr ")") ...
                Kind::Keyword(Keyword::LPAREN) => {
                    loop {
                        let arg = self.parse_expression()?;
                        self.expect_keyword(Keyword::RPAREN)?;
                        node = Node::new_apply(node, arg);

                        token = self.next_token()?;

                        if !token.has_keyword(&Keyword::DOT) {
                            self.unget_token(token);
                            break;
                        } else {
                            self.expect_keyword(Keyword::LPAREN)?;
                        }
                    }
                },
                // [projection]
                //
                // record "." label
                //
                // label is:
                //        identifier
                //      | nat
                Kind::Identifier(ref s) => {
                    node = Node::new_projection(node, s.clone());
                },
                Kind::Nat(ref i) => {
                    node = Node::new_projection(node, i.to_string());
                },
                _ => {
                    return Err(Error::UnexpectedToken("Identifier or Nat as label".to_string(), token));
                }
            }
            token = self.next_token()?;
        }

        // [type apply]
        //
        // expr "[" type "]"
        if token.has_keyword(&Keyword::LBRACKET) {
            let ty = self.parse_type()?;
            self.expect_keyword(Keyword::RBRACKET)?;
            node = Node::new_ty_apply(node, ty);
            token = self.next_token()?;
        }

        if token.has_keyword(&Keyword::COLONEQ) {
            let node2 = self.parse_expression()?;
            node = Node::new_assign(node, node2);
            token = self.next_token()?;
        }

        if token.has_keyword(&Keyword::AS) {
            let ty = self.parse_type()?;
            Ok(Node::new_as(node, ty))
        } else {
            self.unget_token(token);
            Ok(node)
        }
    }

    // There are 2 types of perse methods
    // (1) First token has been already consumed when methods are called,
    //     e.g. parse_bool, parse_var_ref etc.
    // (2) First token has not been already consumed,
    //     e.g. parse_type.
    fn _parse_expression(&mut self) -> Result<Node, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::Keyword(Keyword::TRUE) => self.parse_bool(true),
            Kind::Keyword(Keyword::FALSE) => self.parse_bool(false),
            Kind::Nat(i) => self.parse_nat(i),
            Kind::Identifier(s) => self.parse_var_ref(s),
            Kind::Keyword(Keyword::ARROW) => self.parse_lambda(),
            Kind::Keyword(Keyword::IF) => self.parse_if(),
            Kind::Keyword(Keyword::ISZERO) => self.parse_iszero(),
            Kind::Keyword(Keyword::SUCC) => self.parse_succ(),
            Kind::Keyword(Keyword::PRED) => self.parse_pred(),
            Kind::Keyword(Keyword::LBRACE) => self.parse_record(),
            Kind::Keyword(Keyword::UNIT) => self.parse_unit(),
            Kind::Keyword(Keyword::LET) => self.parse_let(),
            Kind::Keyword(Keyword::LT) => self.parse_tag(),
            Kind::Keyword(Keyword::CASE) => self.parse_case(),
            Kind::Keyword(Keyword::FIX) => self.parse_fix(),
            Kind::Keyword(Keyword::LETREC) => self.parse_letrec(),
            Kind::Keyword(Keyword::REF) => self.parse_ref(),
            Kind::Keyword(Keyword::BANG) => self.parse_deref(),
            Kind::EOF => Ok(Node::new_none_expression()),
            _ => Err(Error::NotSupported(token))
        }
    }

    fn parse_bool(&mut self, bool: bool) -> Result<Node, Error> {
        Ok(Node::new_bool(bool))
    }

    fn parse_nat(&mut self, i: u32) -> Result<Node, Error> {
        Ok(Node::new_nat(i))
    }

    // "unit"
    fn parse_unit(&mut self) -> Result<Node, Error> {
        Ok(Node::new_unit())
    }

    // "iszero" exp
    fn parse_iszero(&mut self) -> Result<Node, Error> {
        let node = self.parse_expression()?;
        Ok(Node::new_iszero(node))
    }

    // "succ" exp
    fn parse_succ(&mut self) -> Result<Node, Error> {
        let node = self.parse_expression()?;
        Ok(Node::new_succ(node))
    }

    // "pred" exp
    fn parse_pred(&mut self) -> Result<Node, Error> {
        let node = self.parse_expression()?;
        Ok(Node::new_pred(node))
    }

    fn parse_var_ref(&mut self, str: String) -> Result<Node, Error> {
        Ok(Node::new_var_ref(str))
    }

    //   "->" x ":" arrow_type "{" exp "}"
    // | "->" X "{" exp "}"
    //
    // arrow_type is a type of variable x, not a type of whole lambda.
    fn parse_lambda(&mut self) -> Result<Node, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::Identifier(var) => {
                self.expect_keyword(Keyword::COLON)?;
                let ty = self.parse_type()?;
                self.expect_keyword(Keyword::LBRACE)?;
                let node = self.parse_expression()?;
                self.expect_keyword(Keyword::RBRACE)?;

                Ok(Node::new_lambda(var, node, ty))
            },
            Kind::TyIdentifier(var) => {
                self.expect_keyword(Keyword::LBRACE)?;
                let node = self.parse_expression()?;
                self.expect_keyword(Keyword::RBRACE)?;

                Ok(Node::new_ty_abs(var, node))
            },
            _ => Err(Error::UnexpectedToken("Identifier or TyIdentifier expected.".to_string(), token))
        }
    }

    // "let" variable "=" bound_value "in" body
    fn parse_let(&mut self) -> Result<Node, Error> {
        let var = self.expect_identifier()?;
        self.expect_keyword(Keyword::EQ)?;
        let bound_value = self.parse_expression()?;
        self.expect_keyword(Keyword::IN)?;
        let body = self.parse_expression()?;

        Ok(Node::new_let(var, bound_value, body))
    }

    //   "{" fields "}"
    fn parse_record(&mut self) -> Result<Node, Error> {
        let fields = self.parse_fields()?;
        self.expect_keyword(Keyword::RBRACE)?;
        let record = Node::new_record(fields);
        Ok(record)
    }

    // field ("," field) ...
    fn parse_fields(&mut self) -> Result<Vec<(Option<String>, Node)>, Error> {
        let mut v = Vec::new();
        let field = self.parse_field()?;
        v.push(field);

        let mut token = self.next_token()?;

        while token.has_keyword(&Keyword::COMMA) {
            let field2 = self.parse_field()?;
            v.push(field2);
            // Next token of field should be "," or "}", so
            // we can call next_token method here.
            token = self.next_token()?;
        }
        //
        self.unget_token(token);

        Ok(v)
    }

    //   label "=" expr
    // | expr
    //
    // label is:
    //      identifier
    fn parse_field(&mut self) -> Result<(Option<String>, Node), Error> {
        let label_or_expr = self.next_token()?;

        match label_or_expr.kind {
            Kind::Identifier(s) => {
                self.expect_keyword(Keyword::EQ)?;
                let node = self.parse_expression()?;
                Ok((Some(s), node))
            },
            _ => {
                self.unget_token(label_or_expr);
                let node = self.parse_expression()?;
                Ok((None, node))
            }
        }
    }

    // "<" label "=" expr ">" "as" type
    fn parse_tag(&mut self) -> Result<Node, Error> {
        let label = self.expect_identifier()?;
        self.expect_keyword(Keyword::EQ)?;
        let node = self.parse_expression()?;
        self.expect_keyword(Keyword::GT)?;
        self.expect_keyword(Keyword::AS)?;
        let ty = self.parse_type()?;

        Ok(Node::new_tag(label, node, ty))
    }

    // "fix" expr
    fn parse_fix(&mut self) -> Result<Node, Error> {
        let node = self.parse_expression()?;
        Ok(Node::new_fix(node))
    }

    // "ref" expr
    fn parse_ref(&mut self) -> Result<Node, Error> {
        let node = self.parse_expression()?;
        Ok(Node::new_ref(node))
    }

    // "!" expr
    fn parse_deref(&mut self) -> Result<Node, Error> {
        let node = self.parse_expression()?;
        Ok(Node::new_deref(node))
    }

    // "letrec" variable ":" type "=" lambda_body "in" body
    //
    //    "letrec x : T = t1 in t2"
    // is "let x = fix (-> x : T { t1 }) in t2"
    fn parse_letrec(&mut self) -> Result<Node, Error> {
        let var = self.expect_identifier()?;
        self.expect_keyword(Keyword::COLON)?;
        let ty = self.parse_type()?;
        self.expect_keyword(Keyword::EQ)?;
        let lambda_body = self.parse_expression()?;
        self.expect_keyword(Keyword::IN)?;
        let body = self.parse_expression()?;

        let lambda = Node::new_lambda(var.clone(), lambda_body, ty);
        let fix = Node::new_fix(lambda);
        Ok(Node::new_let(var, fix, body))
    }

    // "case" expr "of" "<" label "=" variable ">" "=>" expr ("|" "<" label "=" variable ">" "=>" expr) ...
    fn parse_case(&mut self) -> Result<Node, Error> {
        let mut cases = Cases::new();
        let variant = self.parse_expression()?;
        self.expect_keyword(Keyword::OF)?;

        loop {
            self.expect_keyword(Keyword::LT)?;
            let label = self.expect_identifier()?;
            self.expect_keyword(Keyword::EQ)?;
            let var = self.expect_identifier()?;
            self.expect_keyword(Keyword::GT)?;
            self.expect_keyword(Keyword::FARROW)?;
            let expr = self.parse_expression()?;
            cases.insert(label, var, expr);
            let token = self.next_token()?;

            if !token.has_keyword(&Keyword::VBAR) {
                self.unget_token(token);
                break;
            }
        }

        Ok(Node::new_case(variant, cases))
    }

    // "if" cond "then" then_expr "else" else_expr
    fn parse_if(&mut self) -> Result<Node, Error> {
        let cond = self.parse_expression()?;
        self.expect_keyword(Keyword::THEN)?;
        let then_expr = self.parse_expression()?;
        self.expect_keyword(Keyword::ELSE)?;
        let else_expr = self.parse_expression()?;

        Ok(Node::new_if(cond, then_expr, else_expr))
    }

    //   Bool
    // | Nat
    // | Top
    // | Type variable
    fn parse_atomic_type(&mut self) -> Result<Ty, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::Keyword(Keyword::BOOL) => Ok(Ty::new_bool()),
            Kind::Keyword(Keyword::NAT) => Ok(Ty::new_nat()),
            Kind::Keyword(Keyword::TOP) => Ok(Ty::new_top()),
            Kind::TyIdentifier(s) => Ok(Ty::new_id(s.clone(), s.clone())),
            _ => Err(Error::UnexpectedToken("{:?} is not an atomic type".to_string(), token))
        }
    }

    // All types
    //
    //   atomic_type "->" arrow_type  // ArrowType
    // | "<" label ":" type (, label ":" type) ... ">" // VariantType
    // | atomic_type
    fn parse_type(&mut self) -> Result<Ty, Error> {
        let mut token = self.next_token()?;

        let ty1 = match token.kind {
            // Case: "<" label ":" type (, label ":" type) ... ">"
            Kind::Keyword(Keyword::LT) => {
                let mut fields = Fields::new();

                loop {
                    let s = self.expect_identifier()?;
                    self.expect_keyword(Keyword::COLON)?;
                    let ty = self.parse_type()?;
                    fields.insert(s.clone(), Box::new(ty));
                    let token2 = self.next_token()?;

                    if token2.has_keyword(&Keyword::GT) { break; }
                    if !token2.has_keyword(&Keyword::COMMA) {
                        return Err(Error::UnexpectedToken(format!("{:?}", Keyword::COMMA), token2));
                    }
                }

                Ty::new_variant(fields)
            },
            // Case: "{" label ":" type (, label ":" type) ... "}"
            Kind::Keyword(Keyword::LBRACE) => {
                let mut fields = Fields::new();

                loop {
                    let s = self.expect_identifier()?;
                    self.expect_keyword(Keyword::COLON)?;
                    let ty = self.parse_type()?;
                    fields.insert(s.clone(), Box::new(ty));
                    let token2 = self.next_token()?;

                    if token2.has_keyword(&Keyword::RBRACE) { break; }
                    if !token2.has_keyword(&Keyword::COMMA) {
                        return Err(Error::UnexpectedToken(format!("{:?}", Keyword::COMMA), token2));
                    }
                }

                Ty::new_record(fields)
            },
            _ => {
                self.unget_token(token);
                self.parse_atomic_type()?
            }
        };

        token = self.next_token()?;

        // Case: atomic_type "->" arrow_type
        if token.has_keyword(&Keyword::ARROW) {
            let ty2 = self.parse_type()?;
            return Ok(Ty::new_arrow(ty1, ty2));
        }

        // Case: atomic_type
        // In this case this method should consume only one token.
        self.unget_token(token);
        Ok(ty1)
    }

    fn next_token(&mut self) -> Result<Token, Error> {
        if !self.buf.is_empty() {
            return Ok(self.pop_token());
        }

        match self.lexer.next_token() {
            Ok(token) => Ok(token),
            Err(error) => Err(self.build_error(error))
        }
    }

    fn build_error(&self, error: lexer::Error) -> Error {
        match error {
            lexer::Error::UnknownToken(_) => Error::UnknownToken,
            lexer::Error::UnexpectedEOF => Error::UnexpectedEOF
        }
    }

    fn expect_keyword(&mut self, keyword: Keyword) -> Result<(), Error> {
        let token = self.next_token()?;

        if token.has_keyword(&keyword) {
            Ok(())
        } else {
            Err(Error::UnexpectedToken(format!("expect_keyword call: {:?}", keyword), token))
        }
    }

    fn expect_identifier(&mut self) -> Result<String, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::Identifier(s) => Ok(s),
            _ => Err(Error::UnexpectedToken("expect_identifier call: Identifier".to_string(), token))
        }
    }

    fn expect_eof(&mut self) -> Result<(), Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::EOF => Ok(()),
            _ => Err(Error::UnexpectedToken("EOF".to_string(), token))
        }
    }

    fn unget_token(&mut self, token: Token) {
        self.buf.push(token);
    }

    fn pop_token(&mut self) -> Token {
        self.buf.pop().expect("Can not pop from empty buf.")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use node::{Kind, Fields};
    use token::{Kind as TokenKind};
    use ty::{Kind as TyKind, Fields as TyFields};

    #[test]
    fn test_parse_nat() {
        let mut parser = Parser::new(" 11 ".to_string());

        assert_eq!(parser.parse(), Ok(Node::new_nat(11)));
    }

    #[test]
    fn test_parse_iszero() {
        let mut parser = Parser::new(" iszero 10".to_string());

        assert_eq!(parser.parse(), Ok(Node::new_iszero(Node::new_nat(10))));
    }

    #[test]
    fn test_parse_pred() {
        let mut parser = Parser::new(" pred 10".to_string());
        assert_eq!(parser.parse(), Ok(Node::new_pred(Node::new_nat(10))));

        let mut parser = Parser::new(" pred false".to_string());
        assert_eq!(parser.parse(), Ok(Node::new_pred(Node::new_bool(false))));
    }

    #[test]
    fn test_parse_succ() {
        let mut parser = Parser::new(" succ 10".to_string());
        assert_eq!(parser.parse(), Ok(Node::new_nat(11)));

        let mut parser = Parser::new(" succ false".to_string());
        assert_eq!(parser.parse(), Ok(Node::new_succ(Node::new_bool(false))));
    }

    #[test]
    fn test_parse_true() {
        let mut parser = Parser::new(" true ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::Bool(true)
        }));
    }

    #[test]
    fn test_parse_false() {
        let mut parser = Parser::new(" false ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::Bool(false)
        }));
    }

    #[test]
    fn test_parse_true_false() {
        let mut parser = Parser::new(" true false ".to_string());

        assert_eq!(parser.parse(), Err(
            Error::UnexpectedToken("EOF".to_string(), Token {kind: TokenKind::Keyword(Keyword::FALSE)}))
        );
    }

    #[test]
    fn test_parse_as() {
        let mut parser = Parser::new(" false as Bool ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::As(Box::new(Node::new_bool(false)), Box::new(Ty::new_bool()))
        }));

        let mut parser = Parser::new(" 1 as Nat ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::As(Box::new(Node::new_nat(1)), Box::new(Ty::new_nat()))
        }));
    }

    #[test]
    fn test_parse_var_ref() {
        let mut parser = Parser::new(" x ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::VarRef("x".to_string())
        }));
    }

    #[test]
    fn test_parse_lambda() {
        let mut parser = Parser::new(" -> x : Bool -> Bool { false } ".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_arrow(Ty::new_bool(), Ty::new_bool()))
            )}
        ));
    }

    #[test]
    fn test_parse_let() {
        let mut parser = Parser::new(" let x = 1 in false ".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Let(
                "x".to_string(),
                Box::new(Node::new_nat(1)),
                Box::new(Node { kind: Kind::Bool(false) })
            )}
        ));
    }

    #[test]
    fn test_parse_lambda_nested_arrow_type() {
        let mut parser = Parser::new(" -> x : Bool -> Bool -> Bool { false } ".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_arrow(Ty::new_bool(), Ty::new_arrow(Ty::new_bool(), Ty::new_bool())))
            )}
        ));
    }

    #[test]
    fn test_parse_fix() {
        let mut parser = Parser::new("fix -> x : Bool -> Bool { false } ".to_string());
        assert_eq!(parser.parse(), Ok(Node::new_fix(
            Node { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_arrow(Ty::new_bool(), Ty::new_bool()))
            )}
        )));

        let mut parser = Parser::new("fix -> x : Bool { false } ".to_string());
        assert_eq!(parser.parse(), Ok(Node::new_fix(
            Node { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_bool())
            )}
        )));
    }

    #[test]
    fn test_parse_lambda_not_arrow_type() {
        let mut parser = Parser::new(" -> x : Bool { false } ".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Lambda(
                "x".to_string(),
                Box::new(Node{ kind: Kind::Bool(false) }),
                Box::new(Ty::new_bool())
            )}
        ));
    }

    #[test]
    fn test_parse_apply() {
        let mut parser = Parser::new(" x.(y) ".to_string());

        assert_eq!(parser.parse(), Ok(Node {
            kind: Kind::Apply(
                Box::new(Node { kind: Kind::VarRef("x".to_string()) }),
                Box::new(Node { kind: Kind::VarRef("y".to_string()) })
            )
        }));
    }

    #[test]
    fn test_parse_apply_2() {
        let mut parser = Parser::new(" -> x : Bool -> Bool { x }.(false) ".to_string());

        assert_eq!(parser.parse(), Ok(Node {
            kind: Kind::Apply(
                Box::new(Node { kind: Kind::Lambda(
                    "x".to_string(),
                    Box::new(Node { kind: Kind::VarRef("x".to_string()) }),
                    Box::new(Ty::new_arrow(Ty::new_bool(), Ty::new_bool()))
                 )}),
                Box::new(Node { kind: Kind::Bool(false) })
            )
        }));
    }

    #[test]
    fn test_parse_ty_abs() {
        let mut parser = Parser::new(" -> X { false } ".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::TyAbs(
                "X".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
            )}
        ));
    }

    #[test]
    fn test_parse_ty_apply() {
        let mut parser = Parser::new(" -> X { false } [Nat]".to_string());

        assert_eq!(parser.parse(), Ok(
            Node::new_ty_apply(
                Node::new_ty_abs("X".to_string(), Node::new_bool(false)),
                Ty::new_nat()
            )
        ));
    }

    #[test]
    fn test_parse_record() {
        let mut parser = Parser::new(" {10, a=false, true} ".to_string());
        let mut fields = Fields::new();

        fields.insert("0".to_string(), Box::new(Node::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Node::new_bool(false)));
        fields.insert("2".to_string(), Box::new(Node::new_bool(true)));

        assert_eq!(parser.parse(), Ok(Node {
            kind: Kind::Record(fields)
        }));
    }

    #[test]
    fn test_parse_variant_type() {
        let mut parser = Parser::new(" <a:Bool, b:Nat> ".to_string());
        let mut fields = TyFields::new();

        fields.insert("a".to_string(), Box::new(Ty::new_bool()));
        fields.insert("b".to_string(), Box::new(Ty::new_nat()));

        assert_eq!(parser.parse_type(), Ok(Ty {
            kind: TyKind::Variant(fields)
        }));
    }

    #[test]
    fn test_parse_top_type() {
        let mut parser = Parser::new("Top".to_string());
        assert_eq!(parser.parse_type(), Ok(Ty {
            kind: TyKind::Top
        }));
    }

    #[test]
    fn test_parse_type_variable() {
        let mut parser = Parser::new("X".to_string());
        assert_eq!(parser.parse_type(), Ok(Ty {
            kind: TyKind::Id("X".to_string(), "X".to_string())
        }));
    }

    #[test]
    fn test_parse_record_type() {
        let mut parser = Parser::new(" {a:Bool, b:Nat} ".to_string());
        let mut fields = TyFields::new();

        fields.insert("a".to_string(), Box::new(Ty::new_bool()));
        fields.insert("b".to_string(), Box::new(Ty::new_nat()));

        assert_eq!(parser.parse_type(), Ok(Ty {
            kind: TyKind::Record(fields)
        }));
    }

    #[test]
    fn test_parse_record_arrow_type() {
        let mut parser = Parser::new(" {a:Bool, b:Nat} -> {b:Nat} ".to_string());
        let mut f1 = TyFields::new();
        f1.insert("a".to_string(), Box::new(Ty::new_bool()));
        f1.insert("b".to_string(), Box::new(Ty::new_nat()));
        let mut f2 = TyFields::new();
        f2.insert("b".to_string(), Box::new(Ty::new_nat()));

        assert_eq!(parser.parse_type(), Ok(Ty::new_arrow(Ty::new_record(f1), Ty::new_record(f2))));
    }

    #[test]
    fn test_parse_case() {
        let mut parser = Parser::new("case <a=1> as <a:Nat, b:Bool> of <a=x> => x | <b=y> => y".to_string());
        let mut cases = Cases::new();
        let mut ty_fields = TyFields::new();

        cases.insert("a".to_string(), "x".to_string(), Node::new_var_ref("x".to_string()));
        cases.insert("b".to_string(), "y".to_string(), Node::new_var_ref("y".to_string()));

        ty_fields.insert("a".to_string(), Box::new(Ty::new_nat()));
        ty_fields.insert("b".to_string(), Box::new(Ty::new_bool()));

        let node = Node::new_tag("a".to_string(), Node::new_nat(1), Ty::new_variant(ty_fields));

        assert_eq!(parser.parse(), Ok(Node::new_case(node, cases)));
    }

    #[test]
    fn test_parse_projection() {
        let mut parser = Parser::new(" {10, a=false, true}.a ".to_string());
        let mut fields = Fields::new();

        fields.insert("0".to_string(), Box::new(Node::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Node::new_bool(false)));
        fields.insert("2".to_string(), Box::new(Node::new_bool(true)));

        assert_eq!(parser.parse(), Ok(Node {
            kind: Kind::Projection(
                Box::new(Node { kind: Kind::Record(fields) }),
                "a".to_string()
            )
        }));


        let mut parser = Parser::new(" {10, a=false, true}.2 ".to_string());
        let mut fields = Fields::new();

        fields.insert("0".to_string(), Box::new(Node::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Node::new_bool(false)));
        fields.insert("2".to_string(), Box::new(Node::new_bool(true)));

        assert_eq!(parser.parse(), Ok(Node {
            kind: Kind::Projection(
                Box::new(Node { kind: Kind::Record(fields) }),
                "2".to_string()
            )
        }));
    }

    #[test]
    fn test_parse_tag() {
        let mut parser = Parser::new(" <bl=false> as Bool".to_string());
        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Tag(
                "bl".to_string(),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Ty::new_bool())
            )}
        ));

        let mut parser = Parser::new(" <nl=1> as Nat ".to_string());
        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Tag(
                "nl".to_string(),
                Box::new(Node::new_nat(1)),
                Box::new(Ty::new_nat())
            )}
        ));
    }

    #[test]
    fn test_parse_if() {
        let mut parser = Parser::new(" if true then false else true ".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::If(
                Box::new(Node { kind: Kind::Bool(true) }),
                Box::new(Node { kind: Kind::Bool(false) }),
                Box::new(Node { kind: Kind::Bool(true) })
            )}
        ));
    }

    #[test]
    fn test_parse_ref() {
        let mut parser = Parser::new("ref false".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Ref(
                Box::new(Node { kind: Kind::Bool(false) }),
            )}
        ));
    }

    #[test]
    fn test_parse_deref() {
        let mut parser = Parser::new("!false".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Deref(
                Box::new(Node { kind: Kind::Bool(false) }),
            )}
        ));
    }

    #[test]
    fn test_parse_assign() {
        let mut parser = Parser::new("a := b".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Assign(
                Box::new(Node { kind: Kind::VarRef("a".to_string()) }),
                Box::new(Node { kind: Kind::VarRef("b".to_string()) }),
            )}
        ));
    }

    #[test]
    fn test_parse_unit_derived_form() {
        let mut parser = Parser::new("1; false".to_string());

        assert_eq!(parser.parse(), Ok(Node {
            kind: Kind::Apply(
                Box::new(Node { kind: Kind::Lambda(
                    "_".to_string(),
                    Box::new(Node { kind: Kind::Bool(false) }),
                    Box::new(Ty::new_unit())
                 )}),
                Box::new(Node::new_nat(1))
            )
        }));
    }

    #[test]
    fn test_parse_blank() {
        let mut parser = Parser::new("  ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::NoneExpression
        }));
    }
}
