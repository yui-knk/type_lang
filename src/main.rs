extern crate type_lang;
extern crate clap;

use std::process::exit;
use std::io::{self};
// use std::fs::File;
// use std::io::prelude::*;

use type_lang::eval::{Evaluator};
use type_lang::type_check::{TypeChecker};
use type_lang::node::{print_with_indent};
use type_lang::parser;

use clap::{Arg, App};

fn run(string: String, dump_parse: bool) {
    let parser = parser::ProgramParser::new();
    let mut type_checker = TypeChecker::new();
    let mut eval = Evaluator::new();
    let result = match parser.parse(&string) {
        Ok(node) => node,
        Err(err) => {
            eprintln!("parse error: {:?}", err);
            exit(1);
        }
    };

    if dump_parse {
        print_with_indent(&mut io::stdout(), &result, 0, 2);
        println!("{:?}", result);
        exit(0);
    }

    match type_checker.check(&result) {
        Ok(_) => (),
        Err(err) => {
            eprintln!("type_checker error: {:?}", err);
            exit(1);
        }
    };

    let value = match eval.eval(result) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("eval error: Can not eval {:?}", e);
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
                          .arg(Arg::with_name("dump")
                               .long("dump")
                               .value_name("dump_option")
                               .help("dump option")
                               .takes_value(true))
                          .get_matches();

    let dump_parse = match matches.value_of("dump") {
        Some("parse") => true,
        Some(_) => false,
        None => false
    };

    match matches.value_of("eval") {
        Some(str) => run(str.to_string(), dump_parse),
        None => println!("Give input script with -e.")
    };
}
