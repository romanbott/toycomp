//! Reusable pieces for building lexers and LALR(1) parsers.
//!
//! Nothing in this crate knows about the toy language: it only understands
//! regular expressions, token streams and context-free grammars.

mod automata;
mod grammar;
mod lalr;
mod lexer;
mod lr_parser;
mod table;
mod tree_builder;

pub use automata::DFA;
pub use automata::NDFA;
pub use automata::TaggedDFA;
pub use grammar::Grammar;
pub use grammar::Production;
pub use grammar::Symbol;
pub use lalr::LALRAction;
pub use lalr::LALRAutomaton;
pub use lalr::ParseError;
pub use lexer::Dfa;
pub use lexer::DfaData;
pub use lexer::Lexer;
pub use lexer::Pattern;
pub use lexer::StaticDFA;
pub use lexer::Token;
pub use lr_parser::LR1Automaton;
pub use lr_parser::LR1AutomatonState;
pub use lr_parser::LR1Item;
pub use table::Action;
pub use table::Table;
pub use table::TableData;
pub use tree_builder::BasicTreeBuilder;
pub use tree_builder::Node;
pub use tree_builder::TreeBuilder;
pub use tree_builder::TreeBuilderError;
