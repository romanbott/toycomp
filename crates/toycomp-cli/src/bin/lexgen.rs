use std::{fs, path::PathBuf};

use clap::{Parser, ValueEnum};
use toycomp_syntax::{Lexer, TaggedDFA};

#[derive(Parser)]
#[command(author, version, about = "Build a minimized DFA from a lexer spec")]
struct Cli {
    /// Lexer spec file to read.
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
    Dot,
    Bin,
}

fn main() {
    let cli = Cli::parse();

    let source = fs::read_to_string(&cli.input).expect("read lexer spec");
    let lexer: Lexer = source.parse().expect("parse lexer spec");
    let dfa = TaggedDFA::from(&lexer).minimize();

    match cli.emit {
        Format::Stats => {
            println!("lexer: {} DFA states", dfa.num_states());
        }
        Format::Dot => {
            println!("{}", dfa.to_graphviz());
        }
        Format::Bin => {
            let output = cli
                .output
                .expect("--output is required when using --emit bin");
            let bytes =
                bincode::encode_to_vec(dfa, bincode::config::standard()).expect("encode lexer DFA");
            fs::write(output, bytes).expect("write lexer DFA");
        }
    }
}
