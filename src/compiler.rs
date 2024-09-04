use std::{borrow::Borrow, collections::HashMap};
use inkwell::{
    builder::Builder, context::Context, module::Module, passes::PassBuilderOptions, 
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
    types::BasicMetadataTypeEnum, values::{AsValueRef, BasicMetadataValueEnum, BasicValue, BasicValueEnum, FloatValue, FunctionValue, PointerValue}, 
    OptimizationLevel,
};
use crate::{parser::{parse, Expr, Stmt}, resolver::{resolve, Function, Globals}, trace};

macro_rules! trace_compiler {
    ($($arg:tt)*) => {
        if cfg!(debug_assertions) {
            if std::env::var("COMPILER_TRACE").is_ok() {
                trace!("COMPILER", $($arg)*)
            }
        }
    };
}

/// Compile the provided source in the provided context.
/// 
/// **Arguments:**
/// - `source` - String containing the source code to compile.
/// - `context` - The LLVM context to compile in.
/// 
/// **Returns:**
/// 
/// The [Module] of compiled code if successful, otherwise a vector of errors that occured during running.
pub fn compile<'ctx>(source: &str, context: &'ctx Context) -> Result<Module<'ctx>, Vec<String>> {
    // Create necessary LLVM instances
    let builder = context.create_builder();
    let module = context.create_module("main");

    // Parse and resolve the input
    let top_level = parse(source)?;
    let (globals, functions) = resolve(top_level)?;

    let compiler = Compiler { context, builder, module, functions, globals };
    compiler.compile()
}

struct Compiler<'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    module: Module<'ctx>,
    functions: HashMap<String, Function<'ctx>>,
    globals: Globals<'ctx>,
}

impl<'ctx> Compiler<'ctx> {
    fn compile(mut self) -> Result<Module<'ctx>, Vec<String>> {
        trace_compiler!("Compiling module");

        // Compile globals
        self.compile_globals();

        Ok(self.module)
    }

    fn compile_globals(&mut self)  {
        trace_compiler!("Compiling globals");

        // TODO: See if a cleaner solution without the variable clones can work
        let mut values = Vec::new();
        for stmt in self.globals.get_top_level() {
            match stmt {
                Stmt::Expression { expr: Expr::VarDeclar { variable, body } } => {
                    let pointer_value = self.module.add_global(self.context.f64_type(), None, variable);
                    let initialiser = self.compile_global_body(body);
                    pointer_value.set_initializer(&initialiser);
                    values.push((variable.clone(), pointer_value));
                },
                _ => panic!("Attempting to compile non expression top level statement, this indicates the resolver and parser have failed catastrophically"),
            }
        }

        for (variable, value) in values {
            self.globals.set_global_pointer(&variable, value).expect("FATAL: Attempting to set value for uresolved global, this indicates the resolver has failed catastropically");
        }
    }

    // TODO: Update when null initialisation is added 
    /// Compile the body into a value so that the global can be initialised.
    fn compile_global_body(&self, body: &Expr) -> FloatValue<'ctx> {
        // TODO: Need to rework when types are added
        trace_compiler!("Compiling global body: {}", body);
        match body {
            Expr::Binary { op, left, right } => {
                let lhs = self.compile_global_body(left).get_constant().unwrap().0;
                let rhs = self.compile_global_body(right).get_constant().unwrap().0;

                match op {
                    '+' => self.context.f64_type().const_float(lhs + rhs),
                    '-' => self.context.f64_type().const_float(lhs - rhs),
                    '*' => self.context.f64_type().const_float(lhs * rhs),
                    '/' => self.context.f64_type().const_float(lhs / rhs),
                    '<' => {
                        let res = if lhs < rhs { 1f64 } else { 0f64 };
                        self.context.f64_type().const_float(res)
                    },
                    '>' => {
                        let res = if lhs > rhs { 1f64 } else { 0f64 };
                        self.context.f64_type().const_float(res)
                    },
                    _ => { panic!("FATAL: Attempting to compile invalid binary expression, this indicates the parser has failed catasrophically") }
                }
            },
            Expr::Unary { op, right } => {
                match op {
                    '-' => {
                        let val = - self.compile_global_body(right).get_constant().unwrap().0;
                        self.context.f64_type().const_float(val)
                    },
                    _ => { panic!("FATAL: Attempting to compile invalid unary expression, this indicates the parser has failed catasrophically") }
                }
            },
            Expr::Number(number) => self.context.f64_type().const_float(*number),
            Expr::Null => panic!("FATAL: Attempting to resolve null expression, this indicates the parser has failed catasrophically"),
            Expr::VarDeclar { variable: _, body: _ } => panic!("FATAL: Attempting to resolve var declar in a global declaration, this indicates the parser has failed catastrophically"),
            Expr::Call { fn_name: _, args: _ } => panic!("FATAL: Attempting to resolve call in a global declaration, this indicates the resolver has failed catastrophically"),
            Expr::VarAssign { variable: _, body: _ } => panic!("FATAL: Attempting to resolve variable assign in global declaration, this indicates the resolver has failed catasrophically"),
            Expr::Variable(_) => panic!("FATAL: Attempting to resolve variable in global declaration, this indicates the resolver has failed catasrophically"),
        }
    }
}

// // TODO: Re-think some of the architecture here, some of the function signatures are pretty monstorous
//     /// Compile the source code and get the module produced or any errors encountered.
//     pub fn compile(mut self) -> Result<LLVMInfo<'ctx>, &'static str> {
//         for stmt in &self.top_level {
//             match stmt {
//                 Stmt::Function { ref prototype, ref body, is_anon: _ } => _ = Compiler::compile_fn(&mut self.llvm_info, prototype, body)?, // TODO: At some point we will need to collect these in a set of globals
//                 _ => unimplemented!(),
//             }
//         }

//         self.run_optimisations();
//         Ok(self.llvm_info)
//     }

//     /// Compile a given function.
//     fn compile_fn(llvm_info: &mut LLVMInfo<'ctx>, prototype: &Stmt, body: &[Stmt]) -> Result<FunctionValue<'ctx>, &'static str> {
//         // TODO: Maybe deal with this better, altho this error should never occur and cannot be recovered from at this stage
//         trace!("Compiling function");
//         let (name, args) = match prototype {
//             Stmt::Prototype { name, args } => (name, args),
//             _ => panic!("FATAL: Attempting to compile invalid function statement, this indicates the parser has failed catasrophically"),
//         };

//         let function = Compiler::compile_prototype(llvm_info, name, args)?;

//         if body.is_empty() { return Ok(function) }

//         // Prepare to emit IR for function arguments
//         let entry = llvm_info.context.append_basic_block(function, "entry");
//         llvm_info.builder.position_at_end(entry);
//         let mut variables = HashMap::with_capacity(args.len());

//         // Create mutable allocations for the arguments
//         for (i, arg) in function.get_param_iter().enumerate() {
//             let arg_name = args[i].as_str();
//             let alloca = Compiler::create_entry_block_alloca(llvm_info.context, function, arg_name);

//             llvm_info.builder.build_store(alloca, arg).unwrap();
//             variables.insert(args[i].clone(), alloca);
//         }

//         // Compile the function body and provide a return value
//         // TODO: The parser should collect return type info and then any return statements will be compiled in the statement
//         for stmt in body {
//             Compiler::compile_stmt(llvm_info, function, stmt, &mut variables)?;
//         }
//         let return_type = llvm_info.context.f64_type().const_float(0f64);
//         llvm_info.builder.build_return(Some(&return_type)).unwrap();

//         if function.verify(true) {
//             Ok(function)
//         } else {
//             unsafe { function.delete(); }

//             Err("Invalid generated function")
//         }
//     }

//     /// Compile a given prototype.
//     fn compile_prototype(llvm_info: &mut LLVMInfo<'ctx>, name: &str, args: &[String]) -> Result<FunctionValue<'ctx>, &'static str> {
//         trace!("Compiling prototype");
//         // TODO: This function needs to be reworked when types are added
//         let args_types = std::iter::repeat(llvm_info.context.f64_type()).take(args.len()).map(|f| f.into()).collect::<Vec<BasicMetadataTypeEnum>>();

//         let fn_type = llvm_info.context.f64_type().fn_type(args_types.as_slice(), false);
//         let fn_val = llvm_info.module.add_function(name, fn_type, None);

//         for (i, arg) in fn_val.get_param_iter().enumerate() {
//             arg.into_float_value().set_name(args[i].as_str());
//         }

//         Ok(fn_val)
//     }

//     /// Creates a new stack allocation instruction in the entry block of a function.
//     fn create_entry_block_alloca(context: &'ctx Context, fn_value: FunctionValue, name: &str) -> PointerValue<'ctx> {
//         trace!("Creating entry block allocation");
//         let builder = context.create_builder();
//         let entry = fn_value.get_first_basic_block().unwrap();

//         match entry.get_first_instruction() {
//             Some(instr) => builder.position_before(&instr),
//             None => builder.position_at_end(entry),
//         }

//         builder.build_alloca(context.f64_type(), name).unwrap()
//     }

//     // TODO: Need to return local variables from expressions, need to think about it as it will be a bit complex
//     /// Compile a statement.
//     fn compile_stmt(llvm_info: &mut LLVMInfo<'ctx>, parent: FunctionValue, stmt: &Stmt, variables: &mut HashMap<String, PointerValue<'ctx>>) -> Result<Option<(String, PointerValue<'ctx>)>, &'static str> {
//         trace!("Compiling statemement");
//         match stmt {
//             Stmt::Conditional { ref cond, ref then, ref otherwise } => { Compiler::compile_conditional(llvm_info, parent, variables, cond, then, otherwise)?; },
//             Stmt::For { ref start, ref condition, ref step, ref body } => { Compiler::compile_for(llvm_info, parent, variables, start, condition, step, body)?; },
//             Stmt::Expression { expr } => { Compiler::compile_expr(llvm_info, parent, variables, expr)?; },
//             _ => panic!("FATAL: Attempting to compile invalid statement, this indicates the parser has failed catasrophically")
//         }

//         Ok(None)
//     }

//     /// Build the body of some statement, ensuring local variables shadow higher ones.
//     fn build_local_body(llvm_info: &mut LLVMInfo<'ctx>, parent: FunctionValue, variables: &mut HashMap<String, PointerValue<'ctx>>, body: &[Stmt]) -> Result<(), &'static str> {
//         trace!("Compiling local body");
//         let mut local_vars = Vec::new();
//         let mut old_vars = Vec::new();
//         for stmt in body {
//             match Compiler::compile_stmt(llvm_info, parent, stmt, variables)? {
//                 Some((local, ptr)) => {
//                     local_vars.push(local.clone());
//                     match variables.get(&local) {
//                         Some(_) => old_vars.push(variables.remove_entry(&local).unwrap()),
//                         None => { variables.insert(local, ptr); },
//                     }
//                 },
//                 None => {},
//             }
//         }

//         // Remove any variables added in the local scope
//         for var in local_vars { variables.remove(&var); }

//         // Re-add any shadowed variables
//         for (name, value) in old_vars { variables.insert(name, value); }

//         Ok(())
//     }

//     /// Compile conditional.
//     fn compile_conditional(
//         llvm_info: &mut LLVMInfo<'ctx>,
//         parent: FunctionValue,
//         variables: &mut HashMap<String, PointerValue<'ctx>>,
//         cond: &Expr,
//         then: &[Stmt],
//         otherwise: &[Stmt]
//     ) -> Result<(), &'static str> {
//         trace!("Compiling conditional statement");
//         // TODO: Decide how variables work here
//         let context = llvm_info.context;

//         let zero_const = context.f64_type().const_float(0.);
//         let cond = Compiler::compile_expr(llvm_info, parent, variables, cond)?;
//         // TODO: When types are added, will need to change this
//         let cond = llvm_info.builder.build_float_compare(inkwell::FloatPredicate::ONE, cond, zero_const, "ifcond").unwrap();

//         let then_bb = context.append_basic_block(parent, "then");
//         let else_bb = context.append_basic_block(parent, "else");
//         let cont_bb = context.append_basic_block(parent, "ifcont");
//         llvm_info.builder.build_conditional_branch(cond, then_bb, else_bb).unwrap();

//         // TODO: When types are added and return statements are added, these conditional branches will need looking at
//         llvm_info.builder.position_at_end(then_bb);

//         // Build then body
//         Compiler::build_local_body(llvm_info, parent, variables, then)?;

//         llvm_info.builder.build_unconditional_branch(cont_bb).unwrap();
//         let then_bb = llvm_info.builder.get_insert_block().unwrap();
//         let then_val = context.f64_type().const_float(0f64);

//         llvm_info.builder.position_at_end(else_bb);
        
//         // Build otherwise body
//         Compiler::build_local_body(llvm_info, parent, variables, otherwise)?;

//         llvm_info.builder.build_unconditional_branch(cont_bb).unwrap();
//         let else_bb = llvm_info.builder.get_insert_block().unwrap();
//         let else_val = context.f64_type().const_float(0f64);

//         // Build the phi for the if statement
//         llvm_info.builder.position_at_end(cont_bb);
//         let phi = llvm_info.builder.build_phi(context.f64_type(), "iftmp").unwrap();
//         phi.add_incoming(&[(&then_val, then_bb), (&else_val, else_bb)]);

//         Ok(())
//     }

//     /// Compile for loop.
//     fn compile_for(
//         llvm_info: &mut LLVMInfo<'ctx>,
//         parent: FunctionValue, 
//         variables: &mut HashMap<String, PointerValue<'ctx>>, 
//         start: &Expr, 
//         condition: &Expr, 
//         step: &Expr, 
//         body: &[Stmt]
//     ) -> Result<(), &'static str> {
//         trace!("Conpiling for statement");
//         let context = llvm_info.context;

//         // Temporarily disable and thus break for statements whilst we work on the resolver

//         // Compile the starting expression
//         // let start_alloca = Compiler::create_entry_block_alloca(context, parent, var_name);
//         // let start = Compiler::compile_expr(llvm_info, parent, variables, start)?;
//         // llvm_info.builder.build_store(start_alloca, start).unwrap();

//         // // Deal with variable shadowing
//         // let old_val = variables.remove(var_name);
//         // variables.insert(var_name.to_owned(), start_alloca);

//         let loop_bb = context.append_basic_block(parent, "loop");

//         llvm_info.builder.build_unconditional_branch(loop_bb).unwrap();
//         llvm_info.builder.position_at_end(loop_bb);

//         // Build the loop body
//         Compiler::build_local_body(llvm_info, parent, variables, body)?;

//         // Build the step
//         let step = Compiler::compile_expr(llvm_info, parent, variables, step)?;

//         // Build the end condition
//         let end_cond = Compiler::compile_expr(llvm_info, parent, variables, condition)?;

//         // TODO: Will need to re-do this when types are implemented
//         // let curr_var = Compiler::build_load(llvm_info, start_alloca, var_name);
//         // let next_var = llvm_info.builder.build_float_add(curr_var.into_float_value(), step, "nextvar").unwrap();

//         // llvm_info.builder.build_store(start_alloca, next_var).unwrap();

//         let end_cond = llvm_info.builder
//             .build_float_compare(inkwell::FloatPredicate::ONE, end_cond, context.f64_type().const_float(0.0),"loopcond")
//             .unwrap();
//         let after_bb = context.append_basic_block(parent, "afterloop");

//         llvm_info.builder.build_conditional_branch(end_cond, loop_bb, after_bb).unwrap();
//         llvm_info.builder.position_at_end(after_bb);

//         // Deal with variable shadowing
//         // variables.remove(var_name);
//         // if let Some(val) = old_val { variables.insert(var_name.to_owned(), val); }

//         Ok(())
//     }

//     // TODO: This needs re-working when types are added
//     /// Compile an expression
//     fn compile_expr(llvm_info: &mut LLVMInfo<'ctx>, parent: FunctionValue, variables: &mut HashMap<String, PointerValue<'ctx>>, expr: &Expr) -> Result<FloatValue<'ctx>, &'static str> {
//         trace!("Compiling expression");
//         match expr {
//             Expr::Call { ref fn_name, ref args } => Compiler::compile_call_expr(llvm_info, parent, variables, fn_name, args),
//             Expr::Number(num) => Ok(llvm_info.context.f64_type().const_float(*num)),
//             Expr::Variable(ref name) => match variables.get(name.as_str()) {
//                 // TODO: This becomes more complex when we add types
//                 Some(var) => Ok(Compiler::build_load(llvm_info, *var, name.as_str()).into_float_value()),
//                 None => Err("Could not find a matching variable"),
//             },
//             Expr::VarAssign { ref variable, ref body } => {
//                 trace!("Compiling variable assignment");
//                 let body_val = Compiler::compile_expr(llvm_info, parent, variables, body)?;
//                 match variables.get(variable) {
//                     Some(variable) => { _ = llvm_info.builder.build_store(*variable, body_val); },
//                     None => {
//                         let alloca = Compiler::create_entry_block_alloca(llvm_info.context, parent, variable);
//                         _ = llvm_info.builder.build_store(alloca, body_val);
//                     }
//                 }

//                 Ok(body_val)
//             },
//             Expr::Binary { op, ref left, ref right } => {
//                 trace!("Compiling binary expression");
//                 if *op == '=' {
//                     let var_name = match *left.borrow() {
//                         Expr::Variable(ref var_name) => var_name,
//                         _ =>  return Err("Expected variable as left-hand operator of assignment"),
//                     };

//                     let var_val = Compiler::compile_expr(llvm_info, parent, variables, right)?;
//                     let var = variables.get(var_name.as_str()).ok_or("Undefined variable")?;
//                     llvm_info.builder.build_store(*var, var_val).unwrap();
//                     Ok(var_val)
//                 } else {
//                     let lhs = Compiler::compile_expr(llvm_info, parent, variables, left)?;
//                     let rhs = Compiler::compile_expr(llvm_info, parent, variables, right)?;

//                     match op {
//                         '+' => Ok(llvm_info.builder.build_float_add(lhs, rhs, "tmpadd").unwrap()),
//                         '-' => Ok(llvm_info.builder.build_float_sub(lhs, rhs, "tmpsub").unwrap()),
//                         '*' => Ok(llvm_info.builder.build_float_mul(lhs, rhs, "tmpmul").unwrap()),
//                         '/' => Ok(llvm_info.builder.build_float_div(lhs, rhs, "tmpdiv").unwrap()),
//                         '<' => Ok({
//                             let cmp = llvm_info
//                                 .builder
//                                 .build_float_compare(inkwell::FloatPredicate::ULT, lhs, rhs, "tmpcmp")
//                                 .unwrap();

//                                 llvm_info.builder.build_unsigned_int_to_float(cmp, llvm_info.context.f64_type(), "tmpbool").unwrap()
//                         }),
//                         '>' => Ok({
//                             let cmp = llvm_info
//                                 .builder
//                                 .build_float_compare(inkwell::FloatPredicate::UGT, lhs, rhs, "tmpcmp")
//                                 .unwrap();

//                                 llvm_info.builder.build_unsigned_int_to_float(cmp, llvm_info.context.f64_type(), "tmpbool").unwrap()
//                         }),
//                         _ => { panic!("FATAL: Attempting to compile invalid binary expression, this indicates the parser has failed catasrophically") }
//                     }
//                 }
//             },
//             Expr::Unary { ref op, ref right } => {
//                 trace!("Compiling unary expression");
//                 match op {
//                     '-' => {
//                         let val = Compiler::compile_expr(llvm_info, parent, variables, right)?;
//                         Ok(llvm_info.builder.build_float_neg(val, "tempneg").unwrap())
//                     },
//                     _ => { panic!("FATAL: Attempting to compile invalid unary expression, this indicates the parser has failed catasrophically") }
//                 }
//             },
//             Expr::Null => Ok(llvm_info.context.f64_type().const_float(0f64)),
//             _ => unimplemented!()
//         }
//     }

//     // TODO: Types will make this more complex
//     /// Compile a call expression
//     fn compile_call_expr(llvm_info: &mut LLVMInfo<'ctx>, parent: FunctionValue, variables: &mut HashMap<String, PointerValue<'ctx>>, fn_name: &str, args: &[Expr]) -> Result<FloatValue<'ctx>, &'static str> {
//         trace!("Compiling call expression");
//         match variables.get(fn_name) {
//             Some(fun) => {
//                 // This is probably naughty
//                 let fn_value = unsafe { FunctionValue::new(fun.as_value_ref()).unwrap() };

//                 let mut compiled_args = Vec::with_capacity(args.len());
//                 for expr in args {
//                     compiled_args.push(Compiler::compile_expr(llvm_info, parent, variables, expr)?);
//                 }

//                 let argsv: Vec<BasicMetadataValueEnum> = compiled_args.iter().by_ref().map(|&val| val.into()).collect();

//                 match llvm_info.builder.build_call(fn_value, &argsv, "tmp").unwrap().try_as_basic_value().left() {
//                     Some(value) => Ok(value.into_float_value()),
//                     None => Err("Invalid call produced"),
//                 }
//             },
//             None => Err("Unknown function"),
//         }
//     }

//     pub fn build_load(llvm_info: &mut LLVMInfo<'ctx>, ptr: PointerValue<'ctx>, name: &str) -> BasicValueEnum<'ctx> {
//         llvm_info.builder.build_load(llvm_info.context.f64_type(), ptr, name).unwrap()
//     }

//     fn run_optimisations(&self) {
//         trace!("Running optimisations");
//         Target::initialize_all(&InitializationConfig::default());
//         let target_triple = TargetMachine::get_default_triple();
//         let target = Target::from_triple(&target_triple).unwrap();
//         let target_machine = target.create_target_machine(
//             &target_triple,
//             "generic",
//             "",
//             OptimizationLevel::None,
//             RelocMode::PIC,
//             CodeModel::Default
//         ).unwrap();
    
//         let passes: &[&str] = &[
//             "instcombine",
//             "reassociate",
//             "gvn",
//             "simplifycfg",
//             // "basic-aa",
//             "mem2reg",
//         ];
    
//         self.llvm_info.module.run_passes(passes.join(",").as_str(), &target_machine, PassBuilderOptions::create()).unwrap();
//     }
// }