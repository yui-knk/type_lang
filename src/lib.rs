extern crate itertools;
#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(pub parser);

pub mod eval;
pub mod node;
pub mod ty;
pub mod type_check;
pub mod token;
pub mod value;

#[cfg(test)]
pub mod parser_test;
