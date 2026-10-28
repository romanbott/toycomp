use std::{fs, path::PathBuf};

use clap::{Parser, ValueEnum};
use toycomp_syntax::{Grammar, LALRAutomaton, OLALRAutomaton};

#[derive(Parser)]
#[command(author, version, about = "Build a LALR(1) table from a grammar")]
struct Cli {
    /// Grammar file to read.
    input: PathBuf,

    /// What to emit.
    #[arg(long, value_enum, default_value_t = Format::Stats)]
    emit: Format,

    /// Output file. Required for `--emit bin`; defaults to stdout otherwise.
    #[arg(long, short)]
    output: Option<PathBuf>,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum Format {
    Stats,
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
        Format::Bin => {
            let output = cli
                .output
                .expect("--output is required when using --emit bin");
            let owned: OLALRAutomaton = (&lalr).into();
            let bytes = bincode::encode_to_vec(owned, bincode::config::standard())
                .expect("encode LALR table");
            fs::write(output, bytes).expect("write LALR table");
        }
    }
}
