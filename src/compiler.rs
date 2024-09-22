use std::{cell::RefCell, collections::HashMap, iter::{self}, rc::Rc};
use inkwell::{
    basic_block::BasicBlock, builder::Builder, context::Context, module::Module, passes::PassBuilderOptions, targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine}, types::BasicMetadataTypeEnum, values::{BasicMetadataValueEnum, FloatValue, FunctionValue, PointerValue}, OptimizationLevel
};
use crate::{lexer::Token, parser::{parse, Expr, Stmt}, resolver::{resolve, Function, Globals, Scope, Statement, Variable}};

#[cfg(debug_assertions)]
use crate::trace;

// TODO: Documemt module better

macro_rules! trace_compiler {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
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
pub fn compile<'ctx>(source: &[char], context: &'ctx Context) -> Result<Module<'ctx>, Vec<String>> {
    // Create necessary LLVM instances
    let builder = context.create_builder();
    let module = context.create_module("main");
    module.set_triple(&TargetMachine::get_default_triple());

    // Parse and resolve the input
    let top_level = parse(source)?;
    let (globals, functions) = resolve(top_level)?;
    let compiler = Compiler { context, builder, module };
    compiler.compile(globals, functions).map_err(|err| vec![err])
}

struct Compiler<'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    module: Module<'ctx>,
}

impl<'ctx> Compiler<'ctx> {
    fn compile(mut self, mut globals: Globals<'ctx>, functions: HashMap<String, Function<'ctx>>) -> Result<Module<'ctx>, String> {
        trace_compiler!("Compiling module");

        self.compile_globals(&mut globals);
        self.compile_prototypes(&functions, &mut globals);
        self.compile_functions(functions, globals)?;

        // Don't run optimisations when debugging as it makes it harder for a person to understand the IR
        if !cfg!(debug_assertions) {
            self.run_optimisations();
        }

        Ok(self.module)
    }

    /// Compile the global body and set the global's pointer to this value.
    fn compile_globals(&mut self, globals: &mut Globals<'ctx>) {
        trace_compiler!("Compiling globals");

        let mut pointers = Vec::new();
        for stmt in globals.get_top_level() {
            match stmt {
                Stmt::Expression { expr: Expr::VarDeclar { variable, body } } => {
                    let pointer_value = self.module.add_global(self.context.f64_type(), None, variable);
                    let initialiser = self.compile_global_body(body);
                    pointer_value.set_initializer(&initialiser);
                    pointers.push((variable.clone(), pointer_value));
                },
                _ => panic!("FATAL: Attempting to compile non-expression top level statement, this indicates a programmer error in the resolver has caused a catasrophic crash"),
            }
        }

        pointers.iter().for_each(|(name, pointer)| globals.set_global_pointer(name, *pointer));
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
                    Token::Plus => self.context.f64_type().const_float(lhs + rhs),
                    Token::Sub => self.context.f64_type().const_float(lhs - rhs),
                    Token::Star => self.context.f64_type().const_float(lhs * rhs),
                    Token::Divide => self.context.f64_type().const_float(lhs / rhs),
                    Token::Less => {
                        let res = if lhs < rhs { 1f64 } else { 0f64 };
                        self.context.f64_type().const_float(res)
                    },
                    Token::Greater => {
                        let res = if lhs > rhs { 1f64 } else { 0f64 };
                        self.context.f64_type().const_float(res)
                    },
                    Token::LessEqual => {
                        let res = if lhs <= rhs { 1f64 } else { 0f64 };
                        self.context.f64_type().const_float(res)
                    },
                    Token::GreaterEqual => {
                        let res = if lhs >= rhs { 1f64 } else { 0f64 };
                        self.context.f64_type().const_float(res)
                    },
                    Token::EqualEqual => {
                        let res = if lhs == rhs { 1f64 } else { 0f64 };
                        self.context.f64_type().const_float(res)
                    },
                    Token::ExclamEqual => {
                        let res = if lhs != rhs { 1f64 } else { 0f64 };
                        self.context.f64_type().const_float(res)
                    },
                    _ => { panic!("FATAL: Attempting to compile invalid binary expression, this indicates a programmer error in the parser has caused a catasrophic crash") }
                }
            },
            Expr::Unary { op, body, pre: _ } => {
                match op {
                    Token::Sub => {
                        let val = - self.compile_global_body(body).get_constant().unwrap().0;
                        self.context.f64_type().const_float(val)
                    },
                    Token::Exclam => {
                        let val = if self.compile_global_body(body).get_constant().unwrap().0 > 0f64 { 0f64 } else { 1f64 };
                        self.context.f64_type().const_float(val)
                    },
                    _ => { panic!("FATAL: Attempting to compile invalid unary expression, this indicates a programmer error in the parser has caused a catasrophic crash") }
                }
            },
            Expr::Number(number) => self.context.f64_type().const_float(*number),
            Expr::Null => panic!("FATAL: Attempting to resolve null expression, this indicates a programmer error in the parser has caused a catasrophic crash"),
            Expr::VarDeclar { .. } => panic!("FATAL: Attempting to resolve var declar in a global declaration, this indicates a programmer error in the parser has caused a catasrophic crash"),
            Expr::Call { .. } => panic!("FATAL: Attempting to resolve call in a global declaration, this indicates a programmer error in the resolver has caused a catasrophic crash"),
            Expr::VarAssign { .. } => panic!("FATAL: Attempting to resolve variable assign in global declaration, this indicates a programmer error in the resolver has caused a catasrophic crash"),
            Expr::Variable(_) => panic!("FATAL: Attempting to resolve variable in global declaration, this indicates a programmer error in the resolver has caused a catasrophic crash"),
        }
    }

    fn compile_prototypes(&self, functions: &HashMap<String, Function<'ctx>>, globals: &mut Globals<'ctx>) {
        trace_compiler!("Compiling function prototypes");
        functions.iter().for_each(|(name, function)| {
            // Ensure externs are compiled properly
            globals.set_function_pointer(name, self.compile_prototype(name, &mut function.args.borrow_mut(), function.body.is_empty()));
        });
    }

    fn compile_prototype(&self, name: &str, args: &mut Scope<'ctx>, is_extern: bool) -> FunctionValue<'ctx> {
        trace_compiler!("Compiling function prototype");
        let (names, variables): (Vec<String>, Vec<&Rc<RefCell<Variable>>>) = args.iter().map(|(name, variable)| (name.clone(), variable)).unzip();

        // TODO: This needs to be reworked when types are added
        let args_types: Vec<BasicMetadataTypeEnum> = variables.iter().map(|_| self.context.f64_type().into()).collect();

        let function_type = self.context.f64_type().fn_type(args_types.as_slice(), false);
        let function_value = self.module.add_function(name, function_type, None);

        if !is_extern {
            let entry = self.context.append_basic_block(function_value, "entry");
            self.builder.position_at_end(entry);

            for (name, arg) in iter::zip(names, function_value.get_param_iter())  {
                arg.into_float_value().set_name(name.as_str());

                let alloca = self.build_entry_block_allocation(function_value, &name);
                self.builder.build_store(alloca, arg).unwrap();

                args.set_variable_pointer(&name, alloca);
            }
        }

        function_value
    }

    fn compile_functions(&self, functions: HashMap<String, Function<'ctx>>, globals: Globals<'ctx>) -> Result<(), String> {
        trace_compiler!("Compiling functions");

        for (name, function) in functions.iter() {
            // Extern
            if function.body.is_empty() { continue }

            // Get the function
            let function_val = globals.get_function_pointer(name);

            // Position after first basic block before writing the body
            let entry = function_val.get_first_basic_block().unwrap();
            self.builder.position_at_end(entry);

            for stmt in function.body.iter() {
                self.compile_stmt(function_val, stmt, &mut function.scope.borrow_mut());
            }
            
            if !function_val.verify(true) { return Err("Failed to verify function".to_string()) }
        }

        Ok(())
    }

    fn build_entry_block_allocation(&self, function_value: FunctionValue, name: &str) -> PointerValue<'ctx> {
        trace_compiler!("Creating entry block allocation for: {}", name);
        let entry = function_value.get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(instr) => self.builder.position_before(&instr),
            None => self.builder.position_at_end(entry),
        }

        // TODO: Rework when types are added
        self.builder.build_alloca(self.context.f64_type(), name).unwrap()
    }

    fn compile_stmt(&self, parent: FunctionValue, statement: &Statement<'ctx>, scope: &mut Scope<'ctx>) {
        trace_compiler!("Compiling statement"); // TODO: Display the statement.
        match statement {
            Statement::Conditional { .. } => self.compile_conditional(parent, statement, scope),
            Statement::For { .. } => self.compile_for(parent, statement),
            Statement::Return { body } => self.compile_return(parent, body, scope),
            Statement::Expression { expr } => _ = self.compile_expr(parent, expr, scope),
        }
    }

    fn compile_conditional(&self, parent: FunctionValue, statement: &Statement<'ctx>, scope: &mut Scope<'ctx>) {
        trace_compiler!("Compiling conditional statement");
        let (cond, then, otherwise, then_scope, otherwise_scope, returns) = if let Statement::Conditional { cond, then, otherwise, then_scope, otherwise_scope, returns } = statement {
            (cond, then, otherwise, then_scope, otherwise_scope, returns)
        } else {
            panic!("FATAL: The compiler has called conditional on a non-conditional statement, this indicates a programmer error in the compiler has caused a catasrophic crash")
        };

        self.builder.position_at_end(self.builder.get_insert_block().unwrap());

        // TODO: When boolean types are added rework this
        // Compile conditional
        let cond = self.compile_expr(parent, cond, scope);
        let cond = self.builder.build_float_to_unsigned_int(cond, self.context.bool_type(), "tmpcond").unwrap();

        let then_bb = self.context.append_basic_block(parent, "then");
        let otherwise_bb = self.context.append_basic_block(parent, "else");
        let cont_bb = if *returns { None } else { Some(self.context.append_basic_block(parent, "ifcont")) };
        self.builder.build_conditional_branch(cond, then_bb, otherwise_bb).unwrap();

        // Build then body
        self.compile_conditional_branch(parent, then_bb, cont_bb, then, &mut then_scope.borrow_mut());

        // Build otherwise body
        self.compile_conditional_branch(parent, otherwise_bb, cont_bb, otherwise, &mut otherwise_scope.borrow_mut());

        if let Some(cont) = cont_bb {
            self.builder.position_at_end(cont);
        }
    }

    fn compile_conditional_branch(&self, parent: FunctionValue, basic_block: BasicBlock, continuation: Option<BasicBlock>, body: &[Statement<'ctx>], scope: &mut Scope<'ctx>) {
        self.builder.position_at_end(basic_block);

        let mut body_returns = false;
        for stmt in body {
            self.compile_stmt(parent, stmt, scope);

            // Avoid two exits in one basic block
            if let Statement::Return { .. } = stmt { body_returns = true; }
            if let Statement::Conditional { returns, .. } = stmt { body_returns = *returns; }
        }

        if !body_returns {
            self.builder.build_unconditional_branch(continuation.unwrap()).unwrap();
        }
    }

    fn compile_for(&self, parent: FunctionValue, statement: &Statement<'ctx>) {
        trace_compiler!("Compiling for statement");
        let (start, condition, step, body, scope) = if let Statement::For { start, condition, step, body, scope } = statement {
            (start, condition, step, body, scope)
        } else {
            panic!("FATAL: The compiler has called for on a non-for statement, this indicates a programmer error in the compiler has caused a catasrophic crash")
        };

        // Compile the starting expression
        _ = self.compile_expr(parent, start, &mut scope.borrow_mut());

        let loop_bb = self.context.append_basic_block(parent, "loop");
        self.builder.build_unconditional_branch(loop_bb).unwrap();
        self.builder.position_at_end(loop_bb);

        // Build the loop body
        for stmt in body {
            self.compile_stmt(parent, stmt, &mut scope.borrow_mut());
        }

        // Build the step
        _ = self.compile_expr(parent, step, &mut scope.borrow_mut());

        // NOTE: May want to have a specified label i.e. loopcond
        // TODO: When boolean types are added rework this
        // Build the end condition
        let end_cond = self.compile_expr(parent, condition, &mut scope.borrow_mut());
        let end_cond = self.builder.build_float_to_unsigned_int(end_cond, self.context.bool_type(), "tmpcond").unwrap();
        let after_bb = self.context.append_basic_block(parent, "afterloop");

        self.builder.build_conditional_branch(end_cond, loop_bb, after_bb).unwrap();
        self.builder.position_at_end(after_bb);
    }

    fn compile_return(&self, parent: FunctionValue, body: &Expr, scope: &mut Scope<'ctx>) {
        // TODO: This will need fixing when void returns are properly added
        self.builder.build_return(Some(&self.compile_expr(parent, body, scope))).unwrap();
    }

    // TODO: Re-work this and all called functions when types are added
    fn compile_expr(&self, parent: FunctionValue, expression: &Expr, scope: &mut Scope<'ctx>) -> FloatValue<'ctx> {
        trace_compiler!("Compiling expression: {}", expression);
        match expression {
            Expr::Call { function_name, args } => self.compile_call(parent, function_name, args, scope),
            // TODO: Re-work when type literals are added
            Expr::Number(number) => self.context.f64_type().const_float(*number),
            Expr::Variable(name) => self.compile_variable_load(name, scope),
            Expr::VarAssign { variable, body, op } => self.compile_assignment(parent, variable, body, op, scope),
            Expr::VarDeclar { variable, body } => self.compile_declaration(parent, variable, body, scope),
            Expr::Binary { op, left, right } => self.compile_binary(parent, op, left, right, scope),
            Expr::Unary { op, body, pre } => self.compile_unary(parent, op, body, *pre, scope),
            // TODO: Rework when null expressions are properly added
            Expr::Null => unimplemented!()
        }
    }

    fn compile_call(&self, parent: FunctionValue, function_name: &str, args: &[Expr], scope: &mut Scope<'ctx>) -> FloatValue<'ctx> {
        trace_compiler!("Compiling call expression");

        let args: Vec<BasicMetadataValueEnum> = args.iter().map(|arg| self.compile_expr(parent, arg, scope).into()).collect();
        let function_value = scope.get_function_pointer(function_name);

        // TODO: This needs changing when types are added, especially when void types are added
        self.builder.build_call(function_value, &args, "tmp").unwrap().try_as_basic_value().left().unwrap().into_float_value()
    }

    fn compile_variable_load(&self, name: &str, scope: &mut Scope<'ctx>) -> FloatValue<'ctx> {
        trace_compiler!("Compiling variable load");
        let variable = scope.get_variable(name).borrow().get_pointer_value();

        // TODO: Rework when types are added
        self.builder.build_load(self.context.f64_type(), variable, name).unwrap().into_float_value()
    }

    fn compile_assignment(&self, parent: FunctionValue, variable: &str, body: &Expr, op: &Token, scope: &mut Scope<'ctx>) -> FloatValue<'ctx> {
        trace_compiler!("Compiling variable assignment");

        let mut value = self.compile_expr(parent, body, scope);
        let ptr = scope.get_variable(variable).borrow().get_pointer_value();

        match op {
            Token::Equal => self.builder.build_store(ptr, value).unwrap(),
            Token::PlusEqual => {
                let variable = self.builder.build_load(self.context.f64_type(), ptr, variable).unwrap().into_float_value();
                value = self.builder.build_float_add(variable, value, "tmpadd").unwrap();
                self.builder.build_store(ptr, value).unwrap()
            },
            Token::SubEqual => {
                let variable = self.builder.build_load(self.context.f64_type(), ptr, variable).unwrap().into_float_value();
                value = self.builder.build_float_sub(variable, value, "tmpadd").unwrap();
                self.builder.build_store(ptr, value).unwrap()
            },
            Token::MulEqual => {
                let variable = self.builder.build_load(self.context.f64_type(), ptr, variable).unwrap().into_float_value();
                value = self.builder.build_float_mul(variable, value, "tmpadd").unwrap();
                self.builder.build_store(ptr, value).unwrap()
            },
            Token::DivideEqual => {
                let variable = self.builder.build_load(self.context.f64_type(), ptr, variable).unwrap().into_float_value();
                value = self.builder.build_float_div(variable, value, "tmpadd").unwrap();
                self.builder.build_store(ptr, value).unwrap()
            },
            _ => panic!("FATAL: The compiler has attempted to compile an invalid assignment, this indicates a programmer error in the parser has caused a catasrophic crash")
        };

        value
    }

    fn compile_declaration(&self, parent: FunctionValue, variable: &str, body: &Expr, scope: &mut Scope<'ctx>) -> FloatValue<'ctx> {
        trace_compiler!("Compiling variable declaration");

        let cur_location = self.builder.get_insert_block().unwrap();
        let ptr = self.build_entry_block_allocation(parent, variable);
        self.builder.position_at_end(cur_location);
        let value = self.compile_expr(parent, body, scope);
        self.builder.build_store(ptr, value).unwrap();
        scope.set_variable_pointer(variable, ptr);

        value
    }

    fn compile_binary(&self, parent: FunctionValue, op: &Token, left: &Expr, right: &Expr, scope: &mut Scope<'ctx>) -> FloatValue<'ctx> {
        trace_compiler!("Compiling binary expression");

        let lhs = self.compile_expr(parent, left, scope);
        let rhs = self.compile_expr(parent, right, scope);
        match op {
            Token::Plus => self.builder.build_float_add(lhs, rhs, "tmpadd").unwrap(),
            Token::Sub => self.builder.build_float_sub(lhs, rhs, "tmpsub").unwrap(),
            Token::MulEqual => self.builder.build_float_mul(lhs, rhs, "tmpmul").unwrap(),
            Token::Divide => self.builder.build_float_div(lhs, rhs, "tmpdiv").unwrap(),
            // TODO: The comparisons below need to be looked at when types are added
            Token::Less => {
                let cmp = self.builder.build_float_compare(inkwell::FloatPredicate::ULT, lhs, rhs, "tmpcmp").unwrap();
                self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
            },
            Token::Greater => {
                let cmp = self.builder.build_float_compare(inkwell::FloatPredicate::UGT, lhs, rhs, "tmpcmp").unwrap();
                self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
            },
            Token::LessEqual => {
                let cmp = self.builder.build_float_compare(inkwell::FloatPredicate::ULE, lhs, rhs, "tmpcmp").unwrap();
                self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
            },
            Token::GreaterEqual => {
                let cmp = self.builder.build_float_compare(inkwell::FloatPredicate::UGE, lhs, rhs, "tmpcmp").unwrap();
                self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
            },
            Token::EqualEqual => {
                let cmp = self.builder.build_float_compare(inkwell::FloatPredicate::UEQ, lhs, rhs, "tmpcmp").unwrap();
                self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
            },
            Token::ExclamEqual => {
                let cmp = self.builder.build_float_compare(inkwell::FloatPredicate::UNE, lhs, rhs, "tmpcmp").unwrap();
                self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
            },
            _ => { panic!("FATAL: Attempting to compile invalid binary expression, this indicates a programmer error in the parser has caused a catasrophic crash") }
        }
    }

    fn compile_unary(&self, parent: FunctionValue, op: &Token, right: &Expr, pre: bool, scope: &mut Scope<'ctx>) -> FloatValue<'ctx> {
        trace_compiler!("Compiling unary expression");

        // TODO: Rework when types are added
        match op {
            Token::Sub => {
                let val = self.compile_expr(parent, right, scope);
                self.builder.build_float_neg(val, "tempneg").unwrap()
            },
            Token::Exclam => {
                let val = self.compile_expr(parent, right, scope);
                let cmp = self.builder.build_float_compare(inkwell::FloatPredicate::UNE, val, self.context.f64_type().const_float(0f64), "tmpcmp").unwrap();
                self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
            },
            Token::PlusPlus => {
                if pre {
                    let val = self.compile_expr(parent, right, scope);
                    let val = self.builder.build_float_add(val, self.context.f64_type().const_float(1f64), "tmpadd").unwrap();

                    let ptr = match right {
                        Expr::Variable(var) => scope.get_variable(var).borrow().get_pointer_value(),
                        _ => panic!("FATAL: Attempting to compile unary increment on non-variable, this indicates a programmer error in the resolver has caused a catasrophic crash"),
                    };

                    self.builder.build_store(ptr, val).unwrap();
                    val
                } else {
                    let val = self.compile_expr(parent, right, scope);
                    let val_after = self.builder.build_float_add(val, self.context.f64_type().const_float(1f64), "tmpadd").unwrap();

                    let ptr = match right {
                        Expr::Variable(var) => scope.get_variable(var).borrow().get_pointer_value(),
                        _ => panic!("FATAL: Attempting to compile unary increment on non-variable, this indicates a programmer error in the resolver has caused a catasrophic crash"),
                    };

                    self.builder.build_store(ptr, val_after).unwrap();
                    val
                }
            },
            Token::SubSub => {
                if pre {
                    let val = self.compile_expr(parent, right, scope);
                    let val = self.builder.build_float_sub(val, self.context.f64_type().const_float(1f64), "tmpadd").unwrap();

                    let ptr = match right {
                        Expr::Variable(var) => scope.get_variable(var).borrow().get_pointer_value(),
                        _ => panic!("FATAL: Attempting to compile unary decrement on non-variable, this indicates a programmer error in the resolver has caused a catasrophic crash"),
                    };

                    self.builder.build_store(ptr, val).unwrap();
                    val
                } else {
                    let val = self.compile_expr(parent, right, scope);
                    let val_after = self.builder.build_float_sub(val, self.context.f64_type().const_float(1f64), "tmpadd").unwrap();
                    
                    
                    let ptr = match right {
                        Expr::Variable(var) => scope.get_variable(var).borrow().get_pointer_value(),
                        _ => panic!("FATAL: Attempting to compile unary decrement on non-variable, this indicates a programmer error in the resolver has caused a catasrophic crash"),
                    };

                    self.builder.build_store(ptr, val_after).unwrap();
                    val
                }
            },
            _ => { panic!("FATAL: Attempting to compile invalid unary expression, this indicates a programmer error in the parser has caused a catasrophic crash") }
        }
    }

    fn run_optimisations(&self) {
        trace_compiler!("Running optimisations");
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
    
        self.module.run_passes(passes.join(",").as_str(), &target_machine, PassBuilderOptions::create()).unwrap();
    }
}

// TODO: At some point add the ability to run the results and ensuring the output is correct
#[cfg(test)]
mod tests {
    use inkwell::{context::Context, module::Module};

    use super::compile;

    fn test_compile<'ctx>(input: &str, context: &'ctx Context) -> Result<Module<'ctx>, Vec<String>> {
        if !input.is_ascii() { panic!("Testing input must be ASCII") }
        let input: Vec<char> = input.chars().collect();
        compile(&input, context)
    }

    #[test]
    fn test_global() {
        let context = Context::create();
        assert!(test_compile("global var x = 1; fun main() { return x; }", &context).is_ok())
    }

    #[test]
    fn test_if() {
        let context = Context::create();
        assert!(test_compile("fun main() { if (1 < 2) { 1; } else { 2; } return 1; }", &context).is_ok())
    }

    #[test]
    fn test_if_return() {
        let context = Context::create();
        assert!(test_compile("fun main() { if (1 < 2) { return 1; } else { return 2; } }", &context).is_ok())
    }

    #[test]
    fn test_if_partial_return() {
        let context = Context::create();
        assert!(test_compile("fun main() { if (1 < 2) { 1; } else { return 2; } return 1; }", &context).is_ok())
    }

    #[test]
    fn test_nested_if() {
        let context = Context::create();
        assert!(test_compile("fun main() { if (1 < 2) { 1; } else { if (1 < 2) { return 1; } else { return 2; } } return 1; }", &context).is_ok())
    }

    #[test]
    fn test_nested_if_following() {
        let context = Context::create();
        assert!(test_compile("fun main() { if (1 < 2) { 1; } else { if (1 < 2) { 1; } else { 2; } 1; } return 1; }", &context).is_ok())
    }

    #[test]
    fn test_nested_if_following_effect() {
        let context = Context::create();
        assert!(test_compile("fun main() { var x = 1; if (1 < 2) { 1; } else { if (1 < 2) { 1; } else { 2; } x = 1; } return 1; }", &context).is_ok())
    }

    #[test]
    fn test_for() {
        let context = Context::create();
        assert!(test_compile("extern printd(x); fun main() { for (var x = 0; x < 10; x = x + 1) { printd(x); } return 1; }", &context).is_ok())
    }

    #[test]
    fn recursive_fib() {
        let context = Context::create();
        assert!(test_compile("
fun recursive_fib(x) {
    if (x < 3) {
        return 1;
    }
    else {
        return recursive_fib(x - 1) + recursive_fib(x - 2);
    }
} 

fun main() {
    return recursive_fib(10);
}", &context).is_ok())
    }

    #[test]
    fn iterative_fib() {
        let context = Context::create();
        assert!(test_compile("
fun iterative_fib(x) {
    var a = 1;
    var b = 1; 
    var c = 0;
    for (var i = 3; i < x + 1; i = i + 1) {
        c = a + b;
        a = b;
        b = c;
    }

    return c;
}
    
fun main() {
    return iterative_fib(10);
}", &context).is_ok())
    }

    #[test]
    fn shortened_for() {
        let context = Context::create();
        assert!(test_compile("
extern printd(x);

fun main() {
    for (var x = 0; x < 10; x++) {
        printd(x);
    }

    return 1;
}", &context).is_ok())
    }

    #[test]
    fn pre_post() {
        let context = Context::create();
        assert!(test_compile("
extern printd(x);

fun main() {
    var y = 0;
    var z = 0;
    for (var x = 0; x < 10; x++) {
        printd(y++);
        printd(--z);
    }

    return 1;
}", &context).is_ok())
    }
}