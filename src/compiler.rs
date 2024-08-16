use std::{borrow::Borrow, collections::HashMap};

use inkwell::{builder::Builder, context::Context, module::Module, types::BasicMetadataTypeEnum, values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, PointerValue}};

use crate::parser::{Expr, Function, Prototype};

pub struct Compiler<'a, 'ctx> {
    pub context: &'ctx Context,
    pub builder: &'a Builder<'ctx>,
    pub module: &'a Module<'ctx>,
    pub function: &'a Function,
    
    variables: HashMap<String, PointerValue<'ctx>>,
    fn_value_opt: Option<FunctionValue<'ctx>>,
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    pub fn compile(context: &'ctx Context, builder: &'a Builder<'ctx>, module: &'a Module<'ctx>, function: &Function) -> Result<FunctionValue<'ctx>, &'static str> {
        let mut compiler = Compiler {
            context,
            builder,
            module,
            function,
            fn_value_opt: None,
            variables: HashMap::new()
        };

        compiler.compile_fn()
    }

    fn get_function(&self, name: &str) -> Option<FunctionValue<'ctx>> {
        self.module.get_function(name)
    }

    fn fn_value(&self) -> FunctionValue<'ctx> {
        self.fn_value_opt.unwrap()
    }

    /// Creates a new stack allocation instruction in the entry block of the function.
    fn create_entry_block_alloca(&self, name: &str) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();
        let entry = self.fn_value().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(instr) => builder.position_before(&instr),
            None => builder.position_at_end(entry),
        }

        builder.build_alloca(self.context.f64_type(), name).unwrap()
    }

    pub fn build_load(&self, ptr: PointerValue<'ctx>, name: &str) -> BasicValueEnum<'ctx> {
        self.builder.build_load(self.context.f64_type(), ptr, name).unwrap()
    }

    fn compile_expr(&mut self, expr: &Expr) -> Result<FloatValue<'ctx>, &'static str> {
        match *expr {
            Expr::Number(num) => Ok(self.context.f64_type().const_float(num)),
            Expr::Variable(ref name) => match self.variables.get(name.as_str()) {
                Some(var) => Ok(self.build_load(*var, name.as_str()).into_float_value()),
                None => Err("Could not find a matching variable"),
            },
            Expr::VarAssign { ref variable, ref body } => {
                let body_val = self.compile_expr(body)?;
                match self.variables.get(variable) {
                    Some(variable) => {
                        self.builder.build_store(*variable, body_val);
                    },
                    None => {
                        let alloca = self.create_entry_block_alloca(&variable);
                        self.builder.build_store(alloca, body_val);
                    }
                }

                Ok(body_val)
            },
            Expr::Binary { op, ref left, ref right } => {
                if op == '=' {
                    let var_name = match *left.borrow() {
                        Expr::Variable(ref var_name) => var_name,
                        _ =>  return Err("Expected variable as left-hand operator of assignment"),
                    };

                    let var_val = self.compile_expr(right)?;
                    let var = self.variables.get(var_name.as_str()).ok_or("Undefined variable")?;
                    self.builder.build_store(*var, var_val).unwrap();
                    Ok(var_val)
                } else {
                    let lhs = self.compile_expr(left)?;
                    let rhs = self.compile_expr(right)?;

                    match op {
                        '+' => Ok(self.builder.build_float_add(lhs, rhs, "tmpadd").unwrap()),
                        '-' => Ok(self.builder.build_float_sub(lhs, rhs, "tmpsub").unwrap()),
                        '*' => Ok(self.builder.build_float_mul(lhs, rhs, "tmpmul").unwrap()),
                        '/' => Ok(self.builder.build_float_div(lhs, rhs, "tmpdiv").unwrap()),
                        '<' => Ok({
                            let cmp = self
                                .builder
                                .build_float_compare(inkwell::FloatPredicate::ULT, lhs, rhs, "tmpcmp")
                                .unwrap();

                            self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
                        }),
                        '>' => Ok({
                            let cmp = self
                                .builder
                                .build_float_compare(inkwell::FloatPredicate::UGT, lhs, rhs, "tmpcmp")
                                .unwrap();

                            self.builder.build_unsigned_int_to_float(cmp, self.context.f64_type(), "tmpbool").unwrap()
                        }),
                        custom => {
                            let mut name = String::from("binary");
                            name.push(custom);

                            match self.get_function(name.as_str()) {
                                Some(fun) => {
                                    match self.builder
                                        .build_call(fun, &[lhs.into(), rhs.into()], "tmpbin").unwrap()
                                        .try_as_basic_value().left()
                                    {
                                        Some(value) => Ok(value.into_float_value()),
                                        None => Err("Invalid call poduced"),
                                    }
                                },
                                None => Err("Undeifned binary operator"),
                            }
                        },
                    }
                }
            },
            Expr::Unary { ref op, ref right } => {
                match op {
                    '-' => {
                        let val = self.compile_expr(right)?;
                        Ok(self.builder.build_float_neg(val, "tempneg").unwrap())
                    },
                    _ => { panic!()  }
                }
            },
            Expr::Call { ref fn_name, ref args } => match self.get_function(fn_name.as_str()) {
                Some(fun) => {
                    let mut compiled_args = Vec::with_capacity(args.len());
                    for arg in args {
                        compiled_args.push(self.compile_expr(arg)?);
                    }

                    let argsv: Vec<BasicMetadataValueEnum> = compiled_args.iter().by_ref().map(|&val| val.into()).collect();

                    match self.builder
                        .build_call(fun, argsv.as_slice(), "tmp").unwrap()
                        .try_as_basic_value().left()
                    {
                        Some(value) => Ok(value.into_float_value()),
                        None => Err("Invalid call produced"),
                    }
                },
                None => Err("Unknown function"),
            },
            Expr::Conditional { ref cond, ref then, ref otherwise } => {
                let parent = self.fn_value();
                let zero_const = self.context.f64_type().const_float(0.);

                let cond = self.compile_expr(cond)?;
                let cond = self.builder.build_float_compare(inkwell::FloatPredicate::ONE, cond, zero_const, "ifcond").unwrap();

                let then_bb = self.context.append_basic_block(parent, "then");
                let else_bb = self.context.append_basic_block(parent, "else");
                let cont_bb = self.context.append_basic_block(parent, "ifcont");

                self.builder.build_conditional_branch(cond, then_bb, else_bb).unwrap();

                self.builder.position_at_end(then_bb);
                // TODO: This requires that we treat the conditional flow as an expression and return a value, think about and fix this
                let mut then_val = self.context.f64_type().const_float(0f64);
                for expr in then {
                    then_val = self.compile_expr(expr)?;
                }
                self.builder.build_unconditional_branch(cont_bb).unwrap();
                let then_bb = self.builder.get_insert_block().unwrap();

                self.builder.position_at_end(else_bb);
                let mut else_val = self.context.f64_type().const_float(0f64);
                for expr in otherwise {
                    else_val = self.compile_expr(expr)?;
                }
                self.builder.build_unconditional_branch(cont_bb).unwrap();
                let else_bb = self.builder.get_insert_block().unwrap();

                self.builder.position_at_end(cont_bb);
                let phi = self.builder.build_phi(self.context.f64_type(), "iftmp").unwrap();
                phi.add_incoming(&[(&then_val, then_bb), (&else_val, else_bb)]);

                Ok(phi.as_basic_value().into_float_value())
            },
            Expr::For { ref var_name, ref start, ref condition, ref step, ref body } => {
                let parent = self.fn_value();

                let start_alloca = self.create_entry_block_alloca(var_name);
                let start = self.compile_expr(start)?;

                self.builder.build_store(start_alloca, start).unwrap();
                let loop_bb = self.context.append_basic_block(parent, "loop");

                self.builder.build_unconditional_branch(loop_bb).unwrap();
                self.builder.position_at_end(loop_bb);

                let old_val = self.variables.remove(var_name.as_str());
                self.variables.insert(var_name.to_owned(), start_alloca);

                for expr in body {
                    self.compile_expr(expr)?;
                }

                let step = self.compile_expr(step)?;

                let end_cond = self.compile_expr(condition)?;

                let curr_var = self.build_load(start_alloca, var_name);
                let next_var = self.builder.build_float_add(curr_var.into_float_value(), step, "nextvar").unwrap();

                self.builder.build_store(start_alloca, next_var).unwrap();

                let end_cond = self.builder
                    .build_float_compare(inkwell::FloatPredicate::ONE, end_cond, self.context.f64_type().const_float(0.0),"loopcond")
                    .unwrap();
                let after_bb = self.context.append_basic_block(parent, "afterloop");

                self.builder.build_conditional_branch(end_cond, loop_bb, after_bb).unwrap();
                self.builder.position_at_end(after_bb);

                self.variables.remove(var_name);

                if let Some(val) = old_val { self.variables.insert(var_name.to_owned(), val); }

                Ok(self.context.f64_type().const_float(0.0))
            },
            // TODO: This will need changing, currently this is never created by the parser but at some point it may as a default value
            Expr::Null => {
                panic!("This should never happen right now")
            }
        }
    }

    fn compile_prototype(&self, proto: &Prototype) -> Result<FunctionValue<'ctx>, &'static str> {
        let args_types = std::iter::repeat(self.context.f64_type()).take(proto.args.len()).map(|f| f.into()).collect::<Vec<BasicMetadataTypeEnum>>();
        let args_types = args_types.as_slice();

        let fn_type = self.context.f64_type().fn_type(args_types, false);
        let fn_val = self.module.add_function(proto.name.as_str(), fn_type, None);

        for (i, arg) in fn_val.get_param_iter().enumerate() {
            arg.into_float_value().set_name(proto.args[i].as_str());
        }

        Ok(fn_val)
    }

    fn compile_fn(&mut self) -> Result<FunctionValue<'ctx>, &'static str> {
        let proto = &self.function.prototype;
        let function = self.compile_prototype(proto)?;

        if self.function.body.is_empty() { return Ok(function) }

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);
        self.fn_value_opt = Some(function);
        self.variables.reserve(proto.args.len());

        for (i, arg) in function.get_param_iter().enumerate() {
            let arg_name = proto.args[i].as_str();
            let alloca = self.create_entry_block_alloca(arg_name);

            self.builder.build_store(alloca, arg).unwrap();
            self.variables.insert(proto.args[i].clone(), alloca);
        }

        // TODO: This is a bad way of doing return values, fix it
        let mut return_type = self.context.f64_type().const_float(0f64);
        for stmt in &self.function.body {
            return_type = self.compile_expr(&stmt)?;
        }
        self.builder.build_return(Some(&return_type)).unwrap();

        if function.verify(true) {
            Ok(function)
        } else {
            unsafe {
                function.delete();
            }

            Err("Invalid generated function")
        }
    }
}