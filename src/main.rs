extern crate type_lang;

use std::process::exit;
use type_lang::eval::{Evaluator};
use type_lang::parser::{Parser};


fn main() {
    let mut parser = Parser::new("false".to_string());
    let eval = Evaluator::new();
    let result = match parser.parse() {
        Ok(node) => node,
        Err(err) => {
            eprintln!("error: {:?}", err);
            exit(1);
        }
    };

    let value = match eval.eval(&result) {
        Some(v) => v,
        None => {
            eprintln!("error: Can not eval");
            exit(1);
        }
    };

    println!("{:?}", value);
}
