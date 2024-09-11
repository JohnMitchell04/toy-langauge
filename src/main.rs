use clap::Parser;
use inkwell::context::Context;
use std::{path::PathBuf, process::Command};

mod lexer;
mod parser;
mod resolver;
mod compiler;
mod utils;
mod standard;

// TODO: Expand to take source files
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

    let output = module.print_to_string().to_string();
    if cfg!(debug_assertions) {
        println!("DEBUG: File compiled to IR: \n{}", output);
    }

    let base_path = if let Some(folder) = args.output_folder { folder } else { PathBuf::from("./") };
    if !base_path.exists() {
        std::fs::create_dir(&base_path).expect("Error: Could not create output directory");
    }
    
    // Only write a textual representation of the IR if we are in a debug build
    let ir_path = base_path.join(module.get_name().to_str().unwrap().to_string() + ".ll");
    if cfg!(debug_assertions) {
        std::fs::write(&ir_path, output).expect("Error: Could not write IR to file");
    } else {
        module.write_bitcode_to_path(&ir_path);
    }

    // TODO: This is a bad solution that does not work when the source code is not present
    // Compile the standard library to LLVM IR
    let standard = base_path.join("standard.lib");
    let output = Command::new("rustc")
        .args(["--crate-type=staticlib", "-o", standard.to_str().unwrap(), "./src/standard.rs"])
        .output().expect("Error: Failed to call rustc, check if rustc is present");

    if !output.stderr.is_empty() { eprintln!("Error: Failed to compile standard library with rustc: {}", String::from_utf8_lossy(&output.stderr)); }

    // Compile to native asm with clang
    let clang_path = args.name.map(|name| { base_path.join(name + ".out") });
    let output = if let Some(path) = clang_path {
        Command::new("clang").args([ir_path.to_str().unwrap(), "-o", path.to_str().unwrap(), "standard.lib"]).output()
    } else {
        Command::new("clang").args([ir_path.to_str().unwrap(), "standard.lib"]).output()
    };

    let output = output.expect("Error: Failed to call clang, check if Clang is present");
    if !output.stderr.is_empty() { eprintln!("Error: Failed to compile with clang: {}", String::from_utf8_lossy(&output.stderr)); }
}
