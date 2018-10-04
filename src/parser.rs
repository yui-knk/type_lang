use lexer;
use node::{Node};
use token::{Kind, Keyword, Token};
use ty::Ty;

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
        let node = self.parse_expression()?;

        self.expect_eof()?;
        Ok(node)
    }

    // There are 2 types of perse methods
    // (1) First token has been already consumed when methods are called,
    //     e.g. parse_bool, parse_var_ref etc.
    // (2) First token has not been already consumed,
    //     e.g. parse_type.
    fn parse_expression(&mut self) -> Result<Node, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::Keyword(Keyword::TRUE) => self.parse_bool(true),
            Kind::Keyword(Keyword::FALSE) => self.parse_bool(false),
            Kind::Nat(i) => self.parse_nat(i),
            Kind::Identifier(s) => self.parse_var_ref(s),
            Kind::Keyword(Keyword::ARROW) => self.parse_lambda(),
            Kind::Keyword(Keyword::LPAREN) => self.parse_apply(),
            Kind::Keyword(Keyword::IF) => self.parse_if(),
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

    // "(" exp1 exp2 ")"
    //
    // Use "(" as anchor to solve left recursion problem.
    fn parse_apply(&mut self) -> Result<Node, Error> {
        let node_1 = self.parse_expression()?;
        let node_2 = self.parse_expression()?;
        self.expect_keyword(Keyword::RPAREN)?;

        Ok(Node::new_apply(node_1, node_2))
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

    // Bool
    fn parse_atomic_type(&mut self) -> Result<Ty, Error> {
        self.expect_keyword(Keyword::BOOL)?;

        Ok(Ty::new_bool())
    }

    //   atomic_type "->" arrow_type
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
            Err(Error::UnexpectedToken(format!("{:?}", keyword), token))
        }
    }

    fn expect_identifier(&mut self) -> Result<String, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::Identifier(s) => Ok(s),
            _ => Err(Error::UnexpectedToken("Identifier".to_string(), token))
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
    use node::{Node, Kind};
    use token::{Kind as TokenKind, Keyword, Token};
    use ty::{Ty};

    #[test]
    fn test_parse_nat() {
        let mut parser = Parser::new(" 11 ".to_string());

        assert_eq!(parser.parse(), Ok(Node::new_nat(11)));
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
        let mut parser = Parser::new(" (x y) ".to_string());

        assert_eq!(parser.parse(), Ok(Node {
            kind: Kind::Apply(
                Box::new(Node { kind: Kind::VarRef("x".to_string()) }),
                Box::new(Node { kind: Kind::VarRef("y".to_string()) })
            )
        }));
    }

    #[test]
    fn test_parse_apply_2() {
        let mut parser = Parser::new(" (-> x : Bool -> Bool { x } false) ".to_string());

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
