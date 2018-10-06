use token::{Token, convert_str_to_keyword};

#[derive(Debug)]
pub struct Lexer {
    // Will be changed to trait to use both String and File
    source: String,
    tok: usize,
    cur: usize,
    debug: bool,
    lineno: usize,
}


#[derive(Debug, PartialEq)]
pub enum Error {
    UnknownToken(String),
    UnexpectedEOF,
}

impl Lexer {
    pub fn new(source: String) -> Lexer {
        //   begin      lex.tok      lex.cur        end
        //    |            |            |            |
        //    |------------+------------+------------|
        //                 |<---------->|
        //                     token
        Lexer {
            source: source,
            tok: 0,
            cur: 0,
            lineno: 1,
            debug: false
        }
    }

    pub fn next_token(&mut self) -> Result<Token, Error> {
        self.skip_whitespace();

        if self.is_eof() {
            return Ok(Token::new_eof());
        }

        // Each read methods ensure cur points next char of token
        // after the method call.
        let result = match self.peek_char()? {
            '{' => self.read_lbrace(),
            '}' => self.read_rbrace(),
            '(' => self.read_lparen(),
            ')' => self.read_rparen(),
            ':' => self.read_colon(),
            '=' => self.read_eq(),
            ',' => self.read_comma(),
            '-' => self.read_arrow(),
            'B' => self.read_bool(),
            '0'...'9' => self.read_nat(),
            'a'...'z' => self.read_identifier_or_keyword(),
            '\n' => {
                self.next_line();
                self.next_token()
            },
            _ => Err(Error::UnknownToken(self.peek_char().unwrap().to_string()))
        };

        self.debug(format!("next_token is called. next_token is {:?}", result));

        self.token_flush();
        result
    }

    fn next_line(&mut self)  {
        self.skip_char();
        self.lineno += 1;
    }

    fn skip_whitespace(&mut self) {
        self.skip_while(|c| c == ' ' || c == '\t');
    }

    fn skip_while<F>(&mut self, f: F)
        where F: Fn(char) -> bool
    {
        while !self.is_eof() && f(self.peek_char().unwrap()) {
            self.skip_char();
        }
    }

    fn skip_char(&mut self) {
        self.debug("skip_char is called.".to_string());
        assert_eq!(self.tok, self.cur);
        self.tok += 1;
        self.cur += 1;
    }

    fn next_char(&mut self) {
        self.cur += 1;
        self.debug(format!("next_char is called. next_char is {:?}", self.peek_char()));
    }

    fn next_while<F>(&mut self, f: F)
        where F: Fn(char) -> bool
    {
        while !self.is_eof() && f(self.peek_char().unwrap()) {
            self.next_char();
        }
    }

    fn peek_char(&self) -> Result<char, Error> {
        if self.is_eof() {
            Err(Error::UnexpectedEOF)
        } else {
            Ok(self.source[self.cur..].chars().nth(0).unwrap())
        }
    }

    fn token_flush(&mut self) {
        self.tok = self.cur;
    }

    fn is_eof(&self) -> bool {
       self.cur >= self.source.len()
    }

    fn read_nat(&mut self) -> Result<Token, Error> {
        self.next_while(|c| c.is_digit(10));

        Ok(Token::new_nat(self.token_string().parse::<u32>().unwrap()))
    }

    fn read_identifier_or_keyword(&mut self) -> Result<Token, Error> {
        self.next_while(|c| c.is_alphanumeric());

        match convert_str_to_keyword(self.token_string()) {
            Some(k) => Ok(Token::new_keyword(k)),
            None => Ok(Token::new_identifier(self.token_string().to_string())),
        }
    }

    fn read_lbrace(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_lbrace())
    }

    fn read_rbrace(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_rbrace())
    }

    fn read_lparen(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_lparen())
    }

    fn read_rparen(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_rparen())
    }

    fn read_colon(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_colon())
    }

    fn read_eq(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_eq())
    }

    fn read_comma(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_comma())
    }

    fn read_bool(&mut self) -> Result<Token, Error> {
        self.expect_next_char('o')?;
        self.expect_next_char('o')?;
        self.expect_next_char('l')?;
        self.next_char();

        Ok(Token::new_bool())
    }

    fn read_arrow(&mut self) -> Result<Token, Error> {
        self.expect_next_char('>')?;
        self.next_char();
        Ok(Token::new_arrow())
    }

    fn expect_next_char(&mut self, c: char) -> Result<(), Error> {
        self.next_char();
        if self.peek_char()? == c {
            Ok(())
        } else {
            Err(Error::UnknownToken(self.token_string_n(1).to_string()))
        }
    }

    fn token_string(&self) -> &str {
        &self.source[self.tok .. self.cur]
    }

    fn token_string_n(&self, n: usize) -> &str {
        &self.source[self.tok .. (self.cur + n)]
    }

    fn debug(&self, str: String) {
        if !self.debug { return; }
        eprintln!("{}", str);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use token::{Token, Keyword};

    #[test]
    fn test_next_token_nat() {
        let mut lexer = Lexer::new(" 10 ".to_string());
        assert_eq!(lexer.next_token(), Ok(Token::new_nat(10)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));

        let mut lexer = Lexer::new(" 09 ".to_string());
        assert_eq!(lexer.next_token(), Ok(Token::new_nat(9)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_iszero() {
        let mut lexer = Lexer::new(" iszero ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::ISZERO)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_true() {
        let mut lexer = Lexer::new(" true ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::TRUE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_false() {
        let mut lexer = Lexer::new(" false ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::FALSE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_true_false() {
        let mut lexer = Lexer::new(" true false ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::TRUE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::FALSE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_if_then_else() {
        let mut lexer = Lexer::new(" if then else ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::IF)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::THEN)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::ELSE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_new_lines() {
        let mut lexer = Lexer::new(r#"
            if false
            then false
            else true
        "#.to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::IF)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::FALSE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::THEN)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::FALSE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::ELSE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::TRUE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_succ() {
        let mut lexer = Lexer::new(" succ ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::SUCC)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_pred() {
        let mut lexer = Lexer::new(" pred ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::PRED)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_braces() {
        let mut lexer = Lexer::new("  { } ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::LBRACE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::RBRACE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_parens() {
        let mut lexer = Lexer::new("  ( ) ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::LPAREN)));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::RPAREN)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_parens_with_identifiers() {
        let mut lexer = Lexer::new("  (x y) ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::LPAREN)));
        assert_eq!(lexer.next_token(), Ok(Token::new_identifier("x".to_string())));
        assert_eq!(lexer.next_token(), Ok(Token::new_identifier("y".to_string())));
        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::RPAREN)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_colon() {
        let mut lexer = Lexer::new(" : ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::COLON)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_eq() {
        let mut lexer = Lexer::new(" = ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::EQ)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_comma() {
        let mut lexer = Lexer::new(" , ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::COMMA)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_bool() {
        let mut lexer = Lexer::new(" Bool ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::BOOL)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_arrow() {
        let mut lexer = Lexer::new(" -> ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::ARROW)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_invalid_arrow() {
        let mut lexer = Lexer::new(" -? ".to_string());

        assert_eq!(lexer.next_token(), Err(Error::UnknownToken("-?".to_string())));
    }

    #[test]
    fn test_next_token_identifier() {
        let mut lexer = Lexer::new(" bar".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_identifier("bar".to_string())));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_unknowntoken() {
        let mut lexer = Lexer::new(" !".to_string());

        assert_eq!(lexer.next_token(), Err(Error::UnknownToken("!".to_string())));
        // assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }
}
