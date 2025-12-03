use bincode::{
    Encode, // Bincode v2 uses its own Encode/Decode traits
    config, // Import the config module
};
use clap::{Args, Parser, Subcommand};
use std::{
    fs::{self, File},
    io::{self, BufWriter, Write},
    path::PathBuf,
    process::Output,
};
use toycomp::{AST, ASTBuilder, Codegen, LALR, OLALRAutomaton};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// The output file path
    #[arg(long)]
    output: Option<PathBuf>,
}

fn main() {
    let cli = Cli::parse();

    let output = cli.output.unwrap_or("toycomp_lalr_automaton.bin".into());

    let file = File::create(output).unwrap();

    // 2. Wrap the file in a BufWriter for efficient disk I/O
    let mut writer = BufWriter::new(file);

    // 3. Serialize the struct directly into the writer
    // bincode::serialize_into is often the most performant way to serialize to a file.
    let config = config::standard();

    let lalr = &LALR.clone();
    let automaton: OLALRAutomaton = lalr.into();

    // 2. Use the new function: encode_into_std_write()
    bincode::encode_into_std_write(automaton, &mut writer, config);

    writer.flush();

    // 4. Ensure all buffered data is written to the file
    writer.flush().unwrap();
}
