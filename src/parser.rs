use lexer;
use node::{Node};
use token::{Kind, Keyword, Token};
use ty::{Ty};

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
        let node = self.parse_expression()?;
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
                _ => {
                    return Err(Error::UnexpectedToken("Identifier or Nat as label".to_string(), token));
                }
            }
            token = self.next_token()?;
        }

        self.unget_token(token);
        Ok(node)
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
            Kind::Keyword(Keyword::LET) => self.parse_let(),
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

    // "->" x ":" arrow_type "{" exp "}"
    //
    // arrow_type is a type of variable x, not a type of whole lambda.
    fn parse_lambda(&mut self) -> Result<Node, Error> {
        let var = self.expect_identifier()?;
        self.expect_keyword(Keyword::COLON)?;
        let ty = self.parse_type()?;
        self.expect_keyword(Keyword::LBRACE)?;
        let node = self.parse_expression()?;
        self.expect_keyword(Keyword::RBRACE)?;

        Ok(Node::new_lambda(var, node, ty))
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
    fn parse_atomic_type(&mut self) -> Result<Ty, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::Keyword(Keyword::BOOL) => Ok(Ty::new_bool()),
            Kind::Keyword(Keyword::NAT) => Ok(Ty::new_nat()),
            _ => Err(Error::UnexpectedToken("{:?} is not an atomic type".to_string(), token))
        }
    }

    // All types
    //
    //   atomic_type "->" arrow_type  // ArrowType
    // | "<" label ":" type (, label ":" type) ... ">" // VariantType
    // | atomic_type
    fn parse_type(&mut self) -> Result<Ty, Error> {
        let ty1 = self.parse_atomic_type()?;
        let token = self.next_token()?;

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
    use node::{Kind};
    use token::{Kind as TokenKind};

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
    fn test_parse_blank() {
        let mut parser = Parser::new("  ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::NoneExpression
        }));
    }
}
