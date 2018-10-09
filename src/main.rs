extern crate type_lang;
extern crate clap;

use std::process::exit;
// use std::fs::File;
// use std::io::prelude::*;

use type_lang::eval::{Evaluator};
use type_lang::type_check::{TypeChecker};
use type_lang::parser::{Parser};

use clap::{Arg, App};

fn run(string: String) {
    let mut parser = Parser::new(string);
    let mut type_checker = TypeChecker::new();
    let mut eval = Evaluator::new();
    let result = match parser.parse() {
        Ok(node) => node,
        Err(err) => {
            eprintln!("error: {:?}", err);
            exit(1);
        }
    };

    match type_checker.check(&result) {
        Ok(_) => (),
        Err(err) => {
            eprintln!("error: {:?}", err);
            exit(1);
        }
    };

    let value = match eval.eval(result) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: Can not eval {:?}", e);
            exit(1);
        }
    };

    println!("{:?}", value);
}

// fn run_from_file(file_name: &str) {
//     let file = match File::open(str) {
//         Ok(f) => f,
//         Err(err) => panic!("{:?}", err)
//     };
//     let buf = BufRead::new(file);

//     run();
// }

fn main() {
    let matches = App::new("TypeLang")
                          .arg(Arg::with_name("eval")
                               .short("e")
                               .value_name("input_str")
                               .help("one line of script")
                               .takes_value(true))
                          .get_matches();

    match matches.value_of("eval") {
        Some(str) => run(str.to_string()),
        None => println!("Give input script with -e.")
    };
}
