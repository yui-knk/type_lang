#[derive(Debug, PartialEq)]
pub struct Token {
    pub kind: Kind,
}

#[derive(Debug, PartialEq)]
pub enum Kind {
    Keyword(Keyword),
    EOF, // End of File
}

#[derive(Debug, PartialEq)]
pub enum Keyword {
    TRUE,
    FALSE,
    LBRACE, // '{'
    RBRACE, // '}'
    // IF,
    // THEN,
    // ELSE,
}

use self::Kind::*;

impl Token {
    pub fn new_eof() -> Token {
        Token { kind: EOF }
    }

    pub fn new_keyword(k: Keyword) -> Token {
        Token { kind: Keyword(k) }
    }

    pub fn new_lbrace() -> Token {
        Token { kind: Keyword(Keyword::LBRACE) }
    }

    pub fn new_rbrace() -> Token {
        Token { kind: Keyword(Keyword::RBRACE) }
    }
}

pub fn convert_str_to_keyword(s: &str) -> Option<Keyword> {
    match s {
        "true" => Some(Keyword::TRUE),
        "false" => Some(Keyword::FALSE),
        _ => None
    }
}

