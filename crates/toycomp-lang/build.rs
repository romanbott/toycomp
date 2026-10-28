use std::{env, fs, path::PathBuf};

use toycomp_syntax::{DfaData, Grammar, LALRAutomaton, Lexer, TableData, TaggedDFA};

const GRAMMAR_SPEC: &str = "spec/toy.lang.grammar";
const LEXER_SPEC: &str = "spec/toy.lang.lex";

fn main() {
    println!("cargo:rerun-if-changed={GRAMMAR_SPEC}");
    println!("cargo:rerun-if-changed={LEXER_SPEC}");

    let grammar_src = fs::read_to_string(GRAMMAR_SPEC).expect("read grammar spec");
    let grammar = Grammar::from_str(&grammar_src)
        .expect("parse grammar spec")
        .augment();
    let lalr = LALRAutomaton::from_grammar(&grammar);
    let table = TableData::from_lalr(&grammar, &lalr);

    let lexer_src = fs::read_to_string(LEXER_SPEC).expect("read lexer spec");
    let lexer: Lexer = lexer_src.parse().expect("parse lexer spec");
    let dfa = TaggedDFA::from(&lexer).minimize();
    let dfa_data = DfaData::from_tagged(&dfa);

    let out = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));
    fs::write(out.join("lalr_table.rs"), table.to_rust_source()).expect("write lalr_table.rs");
    fs::write(out.join("lexer_table.rs"), dfa_data.to_rust_source()).expect("write lexer_table.rs");
}
