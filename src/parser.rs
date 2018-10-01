use lexer;
use node::{Node};
use token::{Kind, Keyword, Token};

#[derive(Debug)]
pub struct Parser {
    lexer: lexer::Lexer,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnknownToken,
    UnexpectedToken(String, Token), // expected, actual
    UnexpectedEOF,
    NotSupported,
}


impl Parser {
    pub fn new(source: String) -> Parser {
        Parser {
            lexer: lexer::Lexer::new(source)
        }
    }

    pub fn parse(&mut self) -> Result<Node, Error> {
        self.parse_program()
    }

    fn parse_program(&mut self) -> Result<Node, Error> {
        let node = match self.parse_expression() {
            ok @ Ok(Node {kind: ::node::Kind::NoneExpression}) => return ok,
            Ok(n) => Ok(n),
            err @ Err(_) => return err
        };

        self.expect_eof()?;
        node
    }

    fn parse_expression(&mut self) -> Result<Node, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::Keyword(Keyword::TRUE) => self.parse_bool(true),
            Kind::Keyword(Keyword::FALSE) => self.parse_bool(false),
            Kind::Identifier(s) => self.parse_var_ref(s),
            Kind::Keyword(Keyword::ARROW) => self.parse_lambda(),
            Kind::EOF => Ok(Node::new_none_expression()),
            _ => Err(Error::NotSupported)
        }
    }

    fn parse_bool(&mut self, bool: bool) -> Result<Node, Error> {
        Ok(Node::new_expression(Node::new_bool(bool)))
    }

    fn parse_var_ref(&mut self, str: String) -> Result<Node, Error> {
        Ok(Node::new_expression(Node::new_var_ref(str)))
    }

    // -> x { exp }
    fn parse_lambda(&mut self) -> Result<Node, Error> {
        let var = self.expect_identifier()?;
        let _ = self.expect_keyword(Keyword::LBRACE)?;
        let node = self.parse_expression()?;
        let _ = self.expect_keyword(Keyword::RBRACE)?;

        Ok(Node::new_lambda(var, node))
    }

    fn next_token(&mut self) -> Result<Token, Error> {
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

    fn expect_keyword(&mut self, keyword: Keyword) -> Result<Token, Error> {
        let token = self.next_token()?;

        if token.has_keyword(&keyword) {
            Ok(token)
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use node::{Node, Kind};
    use token::{Kind as TokenKind, Keyword, Token};

    #[test]
    fn test_parse_true() {
        let mut parser = Parser::new(" true ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::Expression(
                Box::new(Node{ kind: Kind::Bool(true) })
            )
        }));
    }

    #[test]
    fn test_parse_false() {
        let mut parser = Parser::new(" false ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::Expression(
                Box::new(Node{ kind: Kind::Bool(false) })
            )
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
            kind: Kind::Expression(
                Box::new(Node{ kind: Kind::VarRef("x".to_string()) })
            )
        }));
    }

    #[test]
    fn test_parse_lambda() {
        let mut parser = Parser::new(" -> x { false } ".to_string());

        assert_eq!(parser.parse(), Ok(Node
            { kind: Kind::Lambda("x".to_string(), Box::new(Node
                { kind: Kind::Expression(
                    Box::new(Node { kind: Kind::Bool(false) })
                )}
            ))}
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
