use clap::Parser;
use compiler::Compiler;
use inkwell::context::Context;
use std::{io::Write, path::PathBuf};

mod lexer;
mod parser;
mod compiler;
mod utils;

// TODO: Move these somewhere elese
macro_rules! print_flush {
    ($( $x:expr ),* ) => {
        print!( $($x, )* );
        std::io::stdout().flush().expect("Could not flush standard output");
    };
}

#[no_mangle]
pub extern "C" fn putchard(x: f64) -> f64 {
    print_flush!("{}", x as u8 as char);
    x
}

#[no_mangle]
pub extern "C" fn printd(x: f64) -> f64 {
    println!("{}", x);
    x
}

// TODO: Expand to take multiple paths
/// Define the CLI interface
#[derive(Parser)]
#[command(version, about, long_about = None)]
struct CLI {
    #[arg(short, long)]
    source: PathBuf,

    #[arg[short, long]]
    name: Option<String>,

    #[arg(short, long)]
    output_folder: Option<PathBuf>,
}

fn main() {
    let args = CLI::parse();

    if !args.source.exists() {
        println!("Error: source file: \"{}\", does not exist", args.source.to_string_lossy());
    }

    let input = std::fs::read_to_string(args.source).unwrap();

    let context = Context::create();
    let compiler = match Compiler::new(&input, &context) {
        Ok(compiler) => compiler,
        Err(errors) => {
            println!("Errors encountered when parsing source:");
            for error in errors {
                println!("{}", error)
            }
            return;
        }
    };

    let llvm_info = match compiler.compile() {
        Ok(module) => module,
        Err(err) => {
            println!("Error: compiling function: {}", err);
            return
        }
    };

    let output = llvm_info.module.print_to_string();
    if cfg!(debug_assertions) {
        println!("DEBUG: File compiled to IR: {}", output);
    }

    let mut path = if let Some(folder) = args.output_folder { folder } else { PathBuf::from("./") };
    if let Some(name) = args.name { path.push(name); path.push(".ll")  } else { path.push("out.ll") };
    std::fs::write(path, output.to_string());
}
