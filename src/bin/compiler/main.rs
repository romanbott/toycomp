use clap::{Args, Parser, Subcommand};
use std::{
    fs::{self, File},
    io::{self, BufWriter, Write},
    path::PathBuf,
};
use toycomp::{AST, ASTBuilder, Codegen};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Parse the input file and output the AST
    Parse(CommandArgs),
    /// Compile the input file and output FIS-25 intermediate code
    Compile(CommandArgs),
}

#[derive(Args)]
struct CommandArgs {
    /// The input file path
    #[arg(long)]
    input: PathBuf,

    /// The output file path
    #[arg(long)]
    output: Option<PathBuf>,
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Parse(args) => {
            parse(&args.input, args.output.as_ref());
        }
        Commands::Compile(args) => {
            compile(&args.input, args.output.as_ref());
        }
    }
}

fn parse(input_path: &PathBuf, output_path: Option<&PathBuf>) -> io::Result<()> {
    println!("Reading from: {}", input_path.display());
    let input_content = fs::read_to_string(input_path)?;

    let parser: toycomp::Parser<ASTBuilder, AST> = toycomp::Parser::new();

    let ast = parser.parse(&input_content);

    let ast = match ast {
        Ok(ast) => ast,
        Err(_) => todo!(),
    };

    match output_path {
        // Output path provided: Write to the file, overwriting existing content
        Some(path) => {
            println!("Writing (overwriting) to: {}", path.display());
            let file = File::create(path)?;
            let writer = BufWriter::new(file);
            write_debug(&ast, writer)
        }
        // Output path is None: Print to stdout
        None => {
            println!("Output path not provided. Printing to stdout:");
            let writer = BufWriter::new(io::stdout());
            write_debug(&ast, writer)
        }
    }
}

fn write_debug<T: std::fmt::Debug, W: Write + Sized>(
    data: &T,
    mut buf: BufWriter<W>,
) -> io::Result<()> {
    write!(buf, "{:?}", data)?;

    buf.flush()?;
    Ok(())
}

fn compile(input_path: &PathBuf, output_path: Option<&PathBuf>) -> io::Result<()> {
    println!("Reading from: {}", input_path.display());
    let input_content = fs::read_to_string(input_path)?;

    let parser: toycomp::Parser<ASTBuilder, AST> = toycomp::Parser::new();

    let ast = parser.parse(&input_content);

    let mut cg = Codegen::new();

    let ast = match ast {
        Ok(ast) => ast,
        Err(e) => panic!("{:?}", e),
    };

    match output_path {
        // Output path provided: Write to the file, overwriting existing content
        Some(path) => {
            println!("Writing (overwriting) to: {}", path.display());
            let file = File::create(path)?;
            let mut writer = BufWriter::new(file);
            cg.gen_program(ast, &mut writer)
        }
        // Output path is None: Print to stdout
        None => {
            println!("Output path not provided. Printing to stdout:");
            let mut writer = BufWriter::new(io::stdout());
            cg.gen_program(ast, &mut writer)
        }
    }
}
