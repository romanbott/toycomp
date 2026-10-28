use std::{fs, path::PathBuf};

use clap::{Parser, ValueEnum};
use toycomp_syntax::{DfaData, Lexer, TaggedDFA};

#[derive(Parser)]
#[command(author, version, about = "Build a minimized DFA from a lexer spec")]
struct Cli {
    /// Lexer spec file to read.
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
    Dot,
    Rs,
    #[cfg(feature = "bin-tables")]
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
        Format::Rs => {
            let data = DfaData::from_tagged(&dfa);
            let source = data.to_rust_source();
            match cli.output {
                Some(path) => fs::write(path, source).expect("write lexer source"),
                None => print!("{source}"),
            }
        }
        #[cfg(feature = "bin-tables")]
        Format::Bin => {
            let data = DfaData::from_tagged(&dfa);
            let bytes =
                bincode::encode_to_vec(data, bincode::config::standard()).expect("encode DFA");
            let path = cli
                .output
                .expect("--output is required when using --emit bin");
            fs::write(path, bytes).expect("write DFA");
        }
    }
}
