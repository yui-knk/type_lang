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
            ';' => self.read_semicolon(),
            '=' => self.read_eq_or_farrow(),
            ',' => self.read_comma(),
            '.' => self.read_dot(),
            '-' => self.read_arrow(),
            '|' => self.read_vbar(),
            '<' => self.read_lt(),
            '>' => self.read_gt(),
            '!' => self.read_bang(),
            'B' => self.read_bool(),
            'N' => self.read_nnat(),
            'T' => self.read_top(),
            '0'...'9' => self.read_nat(),
            'a'...'z' => self.read_identifier_or_keyword(),
            'A'...'Z' => self.read_type_identifier(),
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

    fn read_type_identifier(&mut self) -> Result<Token, Error> {
        self.next_while(|c| c.is_alphanumeric());

        Ok(Token::new_ty_identifier(self.token_string().to_string()))
    }

    fn read_vbar(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_vbar())
    }

    fn read_lt(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_lt())
    }

    fn read_gt(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_gt())
    }

    fn read_bang(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_bang())
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

        if self.peek_char()? == '=' {
            self.next_char();
            return Ok(Token::new_coloneq());
        }

        Ok(Token::new_colon())
    }

    fn read_semicolon(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_semicolon())
    }

    fn read_eq_or_farrow(&mut self) -> Result<Token, Error> {
        self.next_char();

        if self.peek_char()? == '>' {
            self.next_char();
            return Ok(Token::new_farrow());
        }

        Ok(Token::new_eq())
    }

    fn read_comma(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_comma())
    }

    fn read_dot(&mut self) -> Result<Token, Error> {
        self.next_char();
        Ok(Token::new_dot())
    }

    fn read_bool(&mut self) -> Result<Token, Error> {
        self.expect_next_char('o')?;
        self.expect_next_char('o')?;
        self.expect_next_char('l')?;
        self.next_char();

        Ok(Token::new_bool())
    }

    fn read_nnat(&mut self) -> Result<Token, Error> {
        self.expect_next_char('a')?;
        self.expect_next_char('t')?;
        self.next_char();

        Ok(Token::new_nnat())
    }

    fn read_top(&mut self) -> Result<Token, Error> {
        self.expect_next_char('o')?;
        self.expect_next_char('p')?;
        self.next_char();

        Ok(Token::new_top())
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
    use token::{Keyword};

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
    fn test_next_token_unit() {
        let mut lexer = Lexer::new(" unit ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::UNIT)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_as() {
        let mut lexer = Lexer::new(" as ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::AS)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_case() {
        let mut lexer = Lexer::new(" case ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::CASE)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_of() {
        let mut lexer = Lexer::new(" of ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::OF)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_vbar() {
        let mut lexer = Lexer::new(" | ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::VBAR)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_fix() {
        let mut lexer = Lexer::new(" fix ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::FIX)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_lt() {
        let mut lexer = Lexer::new(" < ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::LT)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_gt() {
        let mut lexer = Lexer::new(" > ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::GT)));
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
    fn test_next_token_coloneq() {
        let mut lexer = Lexer::new(" := ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::COLONEQ)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_semicolon() {
        let mut lexer = Lexer::new(" ; ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::SEMICOLON)));
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
    fn test_next_token_dot() {
        let mut lexer = Lexer::new(" . ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::DOT)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_bang() {
        let mut lexer = Lexer::new(" ! ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::BANG)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_ref() {
        let mut lexer = Lexer::new(" ref ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::REF)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_let() {
        let mut lexer = Lexer::new(" let ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::LET)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_in() {
        let mut lexer = Lexer::new(" in ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::IN)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_letrec() {
        let mut lexer = Lexer::new(" letrec ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::LETREC)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_bool() {
        let mut lexer = Lexer::new(" Bool ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::BOOL)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_nnat() {
        let mut lexer = Lexer::new(" Nat ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::NAT)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_top() {
        let mut lexer = Lexer::new(" Top ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::TOP)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_arrow() {
        let mut lexer = Lexer::new(" -> ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::ARROW)));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_farrow() {
        let mut lexer = Lexer::new(" => ".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_keyword(Keyword::FARROW)));
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
    fn test_next_token_ty_identifier() {
        let mut lexer = Lexer::new(" X".to_string());

        assert_eq!(lexer.next_token(), Ok(Token::new_ty_identifier("X".to_string())));
        assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }

    #[test]
    fn test_next_token_unknowntoken() {
        let mut lexer = Lexer::new(" ?".to_string());

        assert_eq!(lexer.next_token(), Err(Error::UnknownToken("?".to_string())));
        // assert_eq!(lexer.next_token(), Ok(Token::new_eof()));
    }
}
