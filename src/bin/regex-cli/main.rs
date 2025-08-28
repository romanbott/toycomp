use std::{env, process::exit};
use toycomp::Automaton;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 3 {
        eprintln!("Usage: {} <regex> <string>", args[0]);
        std::process::exit(1);
    }

    let regex = &args[1];
    let string = &args[2];


    let automaton = Automaton::from_regex(regex);

    if automaton.accept(string) {
        println!("matches");
    } else {
        println!("doesn't match");
    }
        exit(0)

}
