use token::{Token, convert_str_to_keyword};

#[derive(Debug)]
pub struct Lexer {
    // Will be changed to trait to use both String and File
    source: String,
    tok: usize,
    cur: usize,    
    // lineno: usize,
}


#[derive(Debug, PartialEq)]
pub enum Error {
    UnknownToken,
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
        }
    }

    pub fn next_token(&mut self) -> Result<Token, Error> {
        self.skip_whitespace();

        if self.is_eof() {
            return Ok(Token::new_eof());
        }

        let result = match self.next_char()? {
            'a'...'z' => self.read_identifier_or_keyword(),
            // '\n' => 
            _ => Err(Error::UnknownToken)
        };

        self.token_flush();
        result
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
        assert_eq!(self.tok, self.cur);
        self.tok += 1;
        self.cur += 1;
    }

    fn next_char(&mut self) -> Result<char, Error> {
        self.cur += 1;
        self.peek_char()
    }

    fn next_while<F>(&mut self, f: F)
        where F: Fn(char) -> bool
    {
        while !self.is_eof() && f(self.peek_char().unwrap()) {
            let _ = self.next_char();
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

    fn read_identifier_or_keyword(&mut self) -> Result<Token, Error> {
        self.next_while(|c| c.is_alphanumeric());

        match convert_str_to_keyword(self.token_string()) {
            Some(k) => Ok(Token::new_keyword(k)),
            None => Err(Error::UnknownToken),
        }
    }

    fn token_string(&self) -> &str {
        &self.source[self.tok .. self.cur]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use token::{Token, Keyword};

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
    fn test_next_token_unknowntoken() {
        let mut lexer = Lexer::new(" bar".to_string());

        assert_eq!(lexer.next_token(), Err(Error::UnknownToken));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }
}
