use std::{fs, path::PathBuf};

use clap::{Parser, ValueEnum};
use toycomp_syntax::{Grammar, LALRAutomaton, TableData};

#[derive(Parser)]
#[command(author, version, about = "Build LALR(1) tables from a grammar")]
struct Cli {
    /// Grammar file to read.
    input: PathBuf,

    /// What to emit.
    #[arg(long, value_enum, default_value_t = Format::Stats)]
    emit: Format,

    /// Output file. Defaults to stdout for text formats; required for bin.
    #[arg(long, short)]
    output: Option<PathBuf>,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum Format {
    Stats,
    Rs,
    #[cfg(feature = "bin-tables")]
    Bin,
}

fn main() {
    let cli = Cli::parse();

    let source = fs::read_to_string(&cli.input).expect("read grammar file");
    let grammar = Grammar::from_str(&source).expect("parse grammar").augment();
    let lalr = LALRAutomaton::from_grammar(&grammar);

    match cli.emit {
        Format::Stats => {
            let max_state = lalr
                .table
                .keys()
                .map(|(state, _)| *state)
                .max()
                .unwrap_or(lalr.initial_state);
            println!(
                "grammar: {} productions, {} non-terminals, {} terminals",
                grammar.productions.len(),
                grammar.non_terminals.len(),
                lalr.terminals.len()
            );
            println!(
                "lalr:   {} states, {} table entries, initial state {}",
                max_state + 1,
                lalr.table.len(),
                lalr.initial_state
            );
        }
        Format::Rs => {
            let data = TableData::from_lalr(&grammar, &lalr);
            let source = data.to_rust_source();
            match cli.output {
                Some(path) => fs::write(path, source).expect("write table source"),
                None => print!("{source}"),
            }
        }
        #[cfg(feature = "bin-tables")]
        Format::Bin => {
            let data = TableData::from_lalr(&grammar, &lalr);
            let bytes =
                bincode::encode_to_vec(data, bincode::config::standard()).expect("encode table");
            let path = cli
                .output
                .expect("--output is required when using --emit bin");
            fs::write(path, bytes).expect("write table");
        }
    }
}
