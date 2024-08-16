use inkwell::{context::Context, module::Module, passes::PassBuilderOptions, targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine}, OptimizationLevel};
use parser::Parser;
use compiler::Compiler;

use std::{fs, io::Write};

mod lexer;
mod parser;
mod compiler;
mod utils;

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

fn run_passes_on(module: &Module) {
    Target::initialize_all(&InitializationConfig::default());
    let target_triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&target_triple).unwrap();
    let target_machine = target.create_target_machine(
        &target_triple,
        "generic",
        "",
        OptimizationLevel::None,
        RelocMode::PIC,
        CodeModel::Default
    ).unwrap();

    let passes: &[&str] = &[
        "instcombine",
        "reassociate",
        "gvn",
        "simplifycfg",
        // "basic-aa",
        "mem2reg",
    ];

    module.run_passes(passes.join(",").as_str(), &target_machine, PassBuilderOptions::create()).unwrap();
}

fn main() {
    let mut args = std::env::args();
    if args.len() != 2 {
        println!("Usage: compiler [path]");
        return;
    }

    // TODO: Improve error handling here
    let path = args.nth(1).unwrap();
    let source = fs::read_to_string(path).expect("Could not read from provided file");

    // TODO: Improve to allow multiple files
    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("main");

    let mut parser = Parser::new(&source);

    let function = match parser.parse() {
        Ok(func) => {
            match Compiler::compile(&context, &builder, &module, &func) {
                Ok(function) => function,
                Err(err) => {
                    println!("!> Error compiling function: {}", err);
                    return;
                },
            }
        },
        Err(_) => {
            println!("Error during parsing:");
            for err in parser.get_errors() {
                println!("Error: {}", err);
            }

            return;
        },
    };

    run_passes_on(&module);

    if cfg!(debug_assertions) {
        println!("-> Expression compiled to IR:");
        function.print_to_stderr();
    }

    let ee = module.create_jit_execution_engine(OptimizationLevel::None).unwrap();

    let fn_name = function.get_name().to_str().unwrap();
    let maybe_fn = unsafe { ee.get_function::<unsafe extern "C" fn() -> f64>(fn_name) };
    let compiled_fn = match maybe_fn {
        Ok(f) => f,
        Err(err) => {
            println!("!> Error during execution: {:?}", err);
            return;
        },
    };

    unsafe {
        println!("=> {}", compiled_fn.call());
    }
}
