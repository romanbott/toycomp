use std::{env, fs, path::PathBuf};

use toycomp_syntax::{Grammar, LALRAutomaton, Lexer, OLALRAutomaton, TaggedDFA};

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
    let owned: OLALRAutomaton = (&lalr).into();

    let lexer_src = fs::read_to_string(LEXER_SPEC).expect("read lexer spec");
    let lexer: Lexer = lexer_src.parse().expect("parse lexer spec");
    let dfa = TaggedDFA::from(&lexer).minimize();

    let config = bincode::config::standard();
    let lalr_bytes = bincode::encode_to_vec(owned, config).expect("encode LALR table");
    let dfa_bytes = bincode::encode_to_vec(dfa, config).expect("encode lexer DFA");

    let out = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));
    fs::write(out.join("lalr.bin"), lalr_bytes).expect("write lalr.bin");
    fs::write(out.join("lexer.bin"), dfa_bytes).expect("write lexer.bin");
}
