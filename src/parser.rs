use lexer;
use node::{Node};
use token::{Kind, Keyword, Token};

#[derive(Debug)]
pub struct Parser {
    lexer: lexer::Lexer,
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedToken,
    UnexpectedEOF,
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
        let token = self.next_token()?;

        match token.kind {
            Kind::Keyword(Keyword::TRUE) => self.parse_bool(true),
            Kind::Keyword(Keyword::FALSE) => self.parse_bool(false),
            Kind::Identifier(s) => self.parse_var_ref(s),
            Kind::EOF => Ok(Node::new_none_expression()),
            _ => Err(Error::UnexpectedToken)
        }
    }

    fn parse_bool(&mut self, bool: bool) -> Result<Node, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::EOF => Ok(Node::new_expression(Node::new_bool(bool))),
            _ => Err(Error::UnexpectedToken)
        }
    }

    fn parse_var_ref(&mut self, str: String) -> Result<Node, Error> {
        let token = self.next_token()?;

        match token.kind {
            Kind::EOF => Ok(Node::new_expression(Node::new_var_ref(str))),
            _ => Err(Error::UnexpectedToken)
        }
    }

    fn next_token(&mut self) -> Result<Token, Error> {
        match self.lexer.next_token() {
            Ok(token) => Ok(token),
            Err(error) => Err(self.build_error(error))
        }
    }

    fn build_error(&self, error: lexer::Error) -> Error {
        match error {
            lexer::Error::UnknownToken(_) => Error::UnexpectedToken,
            lexer::Error::UnexpectedEOF => Error::UnexpectedEOF
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use node::{Node, Kind};

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

        assert_eq!(parser.parse(), Err(Error::UnexpectedToken));
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
    fn test_parse_blank() {
        let mut parser = Parser::new("  ".to_string());

        assert_eq!(parser.parse(), Ok(Node{
            kind: Kind::NoneExpression
        }));
    }
}
