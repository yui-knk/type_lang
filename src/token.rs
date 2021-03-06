#[derive(Debug, PartialEq)]
pub struct Token {
    pub kind: Kind,
}

#[derive(Debug, PartialEq)]
pub enum Kind {
    Keyword(Keyword),
    Identifier(String),
    Nat(u32), // NaturalNumber
    EOF, // End of File
}

#[derive(Debug, PartialEq)]
pub enum Keyword {
    TRUE,
    FALSE,
    LBRACE, // '{'
    RBRACE, // '}'
    LPAREN, // '('
    RPAREN, // ')'
    COLON,  // ':'
    ARROW,  // '->'
    FARROW, // '=>'
    BOOL,   // 'Bool' (type)
    NAT,    // 'Nat' (type)
    TOP,    // 'Top' (type)
    UNITT,  // 'Unit' (type)
    REFT,   // 'Ref' (type)
    IF,
    THEN,
    ELSE,
    ISZERO,    // iszero (function)
    SUCC,      // succ (function)
    PRED,      // pred (function)
    EQ,        // '='
    COMMA,     // ','
    DOT,       // '.'
    UNIT,      // 'unit' (value of Unit type)
    AS,        // 'as'
    LET,       // 'let'
    IN,        // 'in'
    SEMICOLON, // ';'
    CASE,      // 'case'
    OF,        // 'of'
    VBAR,      // '|'
    LT,        // '<'
    GT,        // '>'
    FIX,       // 'fix'
    LETREC,    // 'letrec'
    BANG,      // '!'
    COLONEQ,   // ':='
    REF,       // 'ref'
}

use self::Kind::*;

impl Token {
    pub fn new_eof() -> Token {
        Token { kind: EOF }
    }

    pub fn new_keyword(k: Keyword) -> Token {
        Token { kind: Keyword(k) }
    }

    pub fn new_identifier(str: String) -> Token {
        Token { kind: Identifier(str) }
    }

    pub fn new_lt() -> Token {
        Token { kind: Keyword(Keyword::LT) }
    }

    pub fn new_gt() -> Token {
        Token { kind: Keyword(Keyword::GT) }
    }

    pub fn new_lbrace() -> Token {
        Token { kind: Keyword(Keyword::LBRACE) }
    }

    pub fn new_rbrace() -> Token {
        Token { kind: Keyword(Keyword::RBRACE) }
    }

    pub fn new_lparen() -> Token {
        Token { kind: Keyword(Keyword::LPAREN) }
    }

    pub fn new_rparen() -> Token {
        Token { kind: Keyword(Keyword::RPAREN) }
    }

    pub fn new_colon() -> Token {
        Token { kind: Keyword(Keyword::COLON) }
    }

    pub fn new_unit() -> Token {
        Token { kind: Keyword(Keyword::UNIT) }
    }

    pub fn new_bool() -> Token {
        Token { kind: Keyword(Keyword::BOOL) }
    }

    pub fn new_nnat() -> Token {
        Token { kind: Keyword(Keyword::NAT) }
    }

    pub fn new_top() -> Token {
        Token { kind: Keyword(Keyword::TOP) }
    }

    pub fn new_unitt() -> Token {
        Token { kind: Keyword(Keyword::UNITT) }
    }

    pub fn new_reft() -> Token {
        Token { kind: Keyword(Keyword::REFT) }
    }

    pub fn new_nat(i: u32) -> Token {
        Token { kind: Nat(i) }
    }

    pub fn new_if() -> Token {
        Token { kind: Keyword(Keyword::IF) }
    }

    pub fn new_then() -> Token {
        Token { kind: Keyword(Keyword::THEN) }
    }

    pub fn new_else() -> Token {
        Token { kind: Keyword(Keyword::ELSE) }
    }

    pub fn new_iszero() -> Token {
        Token { kind: Keyword(Keyword::ISZERO) }
    }

    pub fn new_arrow() -> Token {
        Token { kind: Keyword(Keyword::ARROW) }
    }

    pub fn new_farrow() -> Token {
        Token { kind: Keyword(Keyword::FARROW) }
    }

    pub fn new_succ() -> Token {
        Token { kind: Keyword(Keyword::SUCC) }
    }

    pub fn new_pred() -> Token {
        Token { kind: Keyword(Keyword::PRED) }
    }

    pub fn new_eq() -> Token {
        Token { kind: Keyword(Keyword::EQ) }
    }

    pub fn new_let() -> Token {
        Token { kind: Keyword(Keyword::LET) }
    }

    pub fn new_comma() -> Token {
        Token { kind: Keyword(Keyword::COMMA) }
    }

    pub fn new_semicolon() -> Token {
        Token { kind: Keyword(Keyword::SEMICOLON) }
    }

    pub fn new_dot() -> Token {
        Token { kind: Keyword(Keyword::DOT) }
    }

    pub fn new_as() -> Token {
        Token { kind: Keyword(Keyword::AS) }
    }

    pub fn new_in() -> Token {
        Token { kind: Keyword(Keyword::IN) }
    }

    pub fn new_vbar() -> Token {
        Token { kind: Keyword(Keyword::VBAR) }
    }

    pub fn new_fix() -> Token {
        Token { kind: Keyword(Keyword::FIX) }
    }

    pub fn new_letrec() -> Token {
        Token { kind: Keyword(Keyword::LETREC) }
    }

    pub fn new_bang() -> Token {
        Token { kind: Keyword(Keyword::BANG) }
    }

    pub fn new_coloneq() -> Token {
        Token { kind: Keyword(Keyword::COLONEQ) }
    }

    pub fn new_ref() -> Token {
        Token { kind: Keyword(Keyword::REF) }
    }

    pub fn has_keyword(&self, keyword: &Keyword) -> bool {
        match self.kind {
            Kind::Keyword(ref key) if key == keyword => true,
            _ => false
        }
    }
}

pub fn convert_str_to_keyword(s: &str) -> Option<Keyword> {
    match s {
        "true" => Some(Keyword::TRUE),
        "false" => Some(Keyword::FALSE),
        "if" => Some(Keyword::IF),
        "then" => Some(Keyword::THEN),
        "else" => Some(Keyword::ELSE),
        "iszero" => Some(Keyword::ISZERO),
        "succ" => Some(Keyword::SUCC),
        "pred" => Some(Keyword::PRED),
        "unit" => Some(Keyword::UNIT),
        "as" => Some(Keyword::AS),
        "let" => Some(Keyword::LET),
        "in" => Some(Keyword::IN),
        "case" => Some(Keyword::CASE),
        "of" => Some(Keyword::OF),
        "fix" => Some(Keyword::FIX),
        "letrec" => Some(Keyword::LETREC),
        "ref" => Some(Keyword::REF),
        _ => None
    }
}

