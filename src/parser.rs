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
            Kind::Keyword(Keyword::ISZERO) => self.parse_iszero(),
            Kind::Keyword(Keyword::SUCC) => self.parse_succ(),
            Kind::Keyword(Keyword::PRED) => self.parse_pred(),
            Kind::Keyword(Keyword::LBRACE) => self.parse_record_or_projection(),
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

    // "(" exp1 exp2 ")"
    //
    // Use "(" as anchor to solve left recursion problem.
    fn parse_apply(&mut self) -> Result<Node, Error> {
        let node_1 = self.parse_expression()?;
        let node_2 = self.parse_expression()?;
        self.expect_keyword(Keyword::RPAREN)?;

        Ok(Node::new_apply(node_1, node_2))
    }

    //   "{" fields "}"
    // | record "." label
    //
    // label is:
    //        identifier
    //      | nat
    fn parse_record_or_projection(&mut self) -> Result<Node, Error> {
        let fields = self.parse_fields()?;
        self.expect_keyword(Keyword::RBRACE)?;
        let record = Node::new_record(fields);
        let token = self.next_token()?;

        match token.kind {
            // projection
            Kind::Keyword(Keyword::DOT) => {
                let token2 = self.next_token()?;

                match token2.kind {
                    Kind::Identifier(s) => Ok(Node::new_projection(record, s)),
                    Kind::Nat(i) => Ok(Node::new_projection(record, i.to_string())),
                    _ => Err(Error::UnexpectedToken("Identifier or Nat as label".to_string(), token))
                }
            },
            // record
            _ => {
                self.unget_token(token);
                Ok(record)
            }
        }
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
    fn test_parse_record() {
        use std::collections::HashMap;

        let mut parser = Parser::new(" {10, a=false, true} ".to_string());
        let mut fields = HashMap::new();

        fields.insert("0".to_string(), Box::new(Node::new_nat(10)));
        fields.insert("a".to_string(), Box::new(Node::new_bool(false)));
        fields.insert("2".to_string(), Box::new(Node::new_bool(true)));

        assert_eq!(parser.parse(), Ok(Node {
            kind: Kind::Record(fields)
        }));
    }

    #[test]
    fn test_parse_projection() {
        use std::collections::HashMap;

        let mut parser = Parser::new(" {10, a=false, true}.a ".to_string());
        let mut fields = HashMap::new();

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
        let mut fields = HashMap::new();

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
