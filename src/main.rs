use clap::Parser;
use inkwell::context::Context;
use std::{io::Write, path::PathBuf};

mod lexer;
mod parser;
mod resolver;
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
struct Cli {
    #[arg(short, long)]
    source: PathBuf,

    #[arg[short, long]]
    name: Option<String>,

    #[arg(short, long)]
    output_folder: Option<PathBuf>,

    #[cfg(debug_assertions)]
    #[arg(short, long)]
    lexer_trace: bool,

    #[cfg(debug_assertions)]
    #[arg(short, long)]
    parser_trace: bool,

    #[cfg(debug_assertions)]
    #[arg(short, long)]
    resolver_trace: bool,

    #[cfg(debug_assertions)]
    #[arg(short, long)]
    compiler_trace: bool,
}

fn main() {
    let args = Cli::parse();

    if !args.source.exists() {
        println!("Error: source file: \"{}\", does not exist", args.source.to_string_lossy());
        return;
    }
    let input = std::fs::read_to_string(args.source).expect("Error: Could not read file");

    // Set up debug info
    #[cfg(debug_assertions)]
    {
        if args.lexer_trace {
            std::env::set_var("LEXER_TRACE", "1");
        }

        if args.parser_trace {
            std::env::set_var("PARSER_TRACE", "1");
        }

        if args.resolver_trace {
            std::env::set_var("RESOLVER_TRACE", "1");
        }

        if args.compiler_trace {
            std::env::set_var("COMPILER_TRACE", "1");
        }
    }

    let context = Context::create();
    let module = match compiler::compile(&input, &context) {
        Ok(module) => module,
        Err(errors) => {
            println!("Errors encountered when compiling source:");
            for error in errors {
                println!("{}", error)
            }
            return;
        }
    };

    let output = module.print_to_string();
    if cfg!(debug_assertions) {
        println!("DEBUG: File compiled to IR: \n{}", output.to_string());
    }

    let mut path = if let Some(folder) = args.output_folder { folder } else { PathBuf::from("./") };
    if let Some(name) = args.name { path.push(name); path.push(".ll")  } else { path.push("out.ll") };
    
    if std::fs::write(path, output.to_string()).is_err() {
        println!("Error: Could not write IR to file")
    }
}
