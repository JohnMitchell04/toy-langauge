use std::{cell::RefCell, collections::HashMap, rc::Rc};
use inkwell::values::{FunctionValue, GlobalValue, PointerValue};
use crate::parser::{Expr, Stmt};

#[cfg(debug_assertions)]
use crate::trace;

macro_rules! trace_resolver {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
            if std::env::var("RESOLVER_TRACE").is_ok() {
                trace!("RESOLVER", $($arg)*)
            }
        }
    };
}

// TOOD: Add type info
/// Variable type that holds information about its LLVM [PointerValue].
/// 
/// The `pointer_value` is not filled in by the resolver but the compiler adds this information to point to the LLVM value when producing IR.
#[derive(Debug, Clone)]
pub struct Variable<'ctx> {
    pointer_value: Option<PointerValue<'ctx>>
}

impl<'ctx> Variable<'ctx> {
    /// Create a new variable.
    pub fn new() -> Self {
        Variable { pointer_value: None }
    }

    /// Retrieve the variable's pointer value.
    /// 
    /// **Returns**:
    /// 
    /// The [`PointerValue`] if set otherwise [`None`].
    /// 
    /// **Panics:**
    /// 
    /// This method is only expected to be used in the compiler when evaluating a variable load, so the variable must already be initialised.
    /// In the compiler we know this should be the case because the resolver should have caught it if it is not the case, if a panic ever occurs it is
    /// because of programmer error in the resolver, this should never panic if the source is valid.
    pub fn get_pointer_value(&self) -> PointerValue<'ctx> {
        self.pointer_value.expect("FATAL: Value not initialised")
    }

    /// Set the variable's pointer value.
    /// 
    /// **Arguments:**
    /// - `pointer_value` - The [`PointerValue`] to set.
    pub fn set_pointer_value(&mut self, pointer_value: PointerValue<'ctx>) {
        self.pointer_value = Some(pointer_value)
    }
}

/// A scope in the program, containing information about variables declared within it and a parent scope if one exists.
#[derive(Debug, Clone)]
pub struct Scope<'ctx> {
    variables: HashMap<String, Rc<RefCell<Variable<'ctx>>>>,
    up_values: HashMap<String, Rc<RefCell<Variable<'ctx>>>>,
    functions: HashMap<String, Rc<RefCell<Option<FunctionValue<'ctx>>>>>,
    parent: Option<Rc<RefCell<Scope<'ctx>>>>,
}

impl<'ctx> Scope<'ctx> {
    /// Create a new scope with no variables and no parent.
    pub fn new() -> Self {
        Scope { variables: HashMap::new(), up_values: HashMap::new(), functions: HashMap::new(), parent: None }
    }

    /// Get the scope's parent.
    ///
    /// **Returns:**
    /// 
    /// The parent if the scope has one, [`None`] otherwise
    pub fn get_parent(&self) -> Option<Rc<RefCell<Scope<'ctx>>>> {
        self.parent.clone()
    }

    /// Set the scope's parent.
    /// 
    /// **Arguments:**
    /// - `parent` - A reference to the parent.
    fn set_parent(&mut self, parent: Rc<RefCell<Scope<'ctx>>>) {
        self.parent = Some(parent)
    }

    /// Get some variable in the scope.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the variable to retrieve.
    /// 
    /// **Returns:**
    /// 
    /// The [`Variable`] in the scope.
    /// 
    /// **Panics:**
    /// 
    /// This method is only used in the compiler where the variable should exist if the resolver is working correctly,
    /// and once in the resolver when we are sure the variable exists. Thus an option is not returned and instead the method
    /// assumes the variable exists. If this panics it indicates a programmer error
    pub fn get_variable(&self, name: &str) -> Rc<RefCell<Variable<'ctx>>> {
        if let Some(variable) = self.variables.get(name) {
            return variable.clone()
        }

        self.up_values.get(name).cloned().expect("FATAL: Variable not in scope")
    }

    /// Set a variable in the scope. This does not mutate the shared variable, instead it gives the scope shared ownership of a new variable.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the variable to set.
    /// - `variable` - The [`Variable`] to set.
    /// 
    /// **Returns:**
    /// 
    /// [`None`] if the variable is not already present, otherwise the [`Variable`] that was set before.
    fn set_variable(&mut self, name: String, variable: Rc<RefCell<Variable<'ctx>>>) -> Option<Rc<RefCell<Variable<'ctx>>>> {
        self.variables.insert(name, variable)
    }

    /// Set a variable pointing to a higher scope variable. This does not mutate the shared variable, instead it gives the scope shared ownership of a new variable.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the variable to set.
    /// - `variable` - The [`Variable`] to set.
    /// 
    /// **Returns:**
    /// 
    /// [`None`] if the variable is not already present, otherwise [`Variable`] that was set before.
    fn set_up_value(&mut self, name: String, variable: Rc<RefCell<Variable<'ctx>>>) -> Option<Rc<RefCell<Variable<'ctx>>>> {
        self.up_values.insert(name, variable)
    }

    /// Check whether the variable is in scope.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the variable to be checked.
    fn contains_variable(&self, name: &str) -> bool {
        self.variables.contains_key(name) || self.up_values.contains_key(name)
    }

    /// Set a variable's pointer value. This mutates the shared ownership of the value, thus setting the same pointer value for all other owners.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the variable to set.
    /// - `variable` - The [`Variable`] to set.
    /// 
    /// **Panics:**
    /// 
    /// This method is only expected to be used in the compiler when evaluating a variable assignment, so the variable must already be declared.
    /// In the compiler we know this should be the case because the resolver should have caught it if it is not the case, if a panic ever occurs it is
    /// because of programmer error in the resolver, this should never panic if the source is valid.
    pub fn set_variable_pointer(&mut self, name: &str, pointer_value: PointerValue<'ctx>) {
        if let Some(variable) = self.variables.get_mut(name) {
            variable.borrow_mut().set_pointer_value(pointer_value);
            return
        }
    
        self.up_values.get_mut(name).expect("FATAL: Variable not in scope").borrow_mut().set_pointer_value(pointer_value)
    }

    /// Get shared ownership of a function pointer.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function to get.
    fn get_function(&self, name: &str) -> Rc<RefCell<Option<FunctionValue<'ctx>>>> {
        self.functions.get(name).cloned().unwrap()
    }

    /// Get a function pointer.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function pointer to get.
    /// 
    /// **Returns:**
    /// 
    /// The [`FunctionValue`] pointer to the function.
    /// 
    /// **Panics:**
    /// 
    /// This method is only expected to be used in the compiler when evaluating a function call, so the function must already be defined and located.
    /// In the compiler we know this should be the case because the resolver should have caught it if it is not the case, if a panic ever occurs it is
    /// because of programmer error in the resolver, this should never panic if the source is valid.
    pub fn get_function_pointer(&self, name: &str) -> FunctionValue<'ctx> {
        self.functions.get(name).unwrap().borrow().expect("FATAL: Function not initialised")
    }

    /// Add a function to the local scope.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function to add.
    fn add_function(&mut self, name: String, function: Rc<RefCell<Option<FunctionValue<'ctx>>>>) {
        self.functions.insert(name, function);
    }

    /// Check whether the function is already scope.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function to be checked.
    fn contains_function(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    /// Retieve an iterator over the variables.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Rc<RefCell<Variable<'ctx>>>)> {
        self.variables.iter()
    }
}

/// A resolved [Stmt], this differs in that we now have resolved the scopes of the variables referred to in the [Stmt].
pub enum Statement<'ctx> {
    Conditional {
        cond: Expr,
        then: Vec<Statement<'ctx>>,
        otherwise: Vec<Statement<'ctx>>,
        then_scope: Rc<RefCell<Scope<'ctx>>>,
        otherwise_scope: Rc<RefCell<Scope<'ctx>>>,
        returns: bool,
    },
    For {
        start: Expr,
        condition: Expr,
        step: Expr,
        body: Vec<Statement<'ctx>>,
        scope: Rc<RefCell<Scope<'ctx>>>,
    },
    Return {
        body: Expr,
    },
    Expression {
        expr: Expr,
    }
}

/// A function in the program, contains information about variable scope and all statements contained within it.
pub struct Function<'ctx> {
    pub args: Rc<RefCell<Scope<'ctx>>>,
    pub body: Vec<Statement<'ctx>>,
    pub scope: Rc<RefCell<Scope<'ctx>>>,
}

///The global scope of the program, contains the top level statements and global variables.
pub struct Globals<'ctx> {
    stmts: Vec<Stmt>,
    scope: Rc<RefCell<Scope<'ctx>>>,
}

impl<'ctx> Globals<'ctx> {
    /// Create a new global scope.
    pub fn new() -> Self {
        Globals { stmts: Vec::new(), scope: Rc::from(RefCell::from(Scope::new())) }
    }

    /// Set statements in a global scope.
    /// 
    /// **Arguments:**
    /// - `stmts` - The top level statements to add to the global. 
    fn add_top_level(&mut self, stmts: Stmt) {
        self.stmts.push(stmts)
    }

    /// Get the statements in global scope.
    /// 
    /// **Returns:**
    /// 
    /// Slice of all top level statements.
    pub fn get_top_level(&self) -> &[Stmt] {
        &self.stmts
    }

    /// Set a global. This does not mutate the shared variable, instead it gives the scope shared ownership of a new variable.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the global to set.
    /// - `variable` - The [`Variable`] to set.
    /// 
    /// **Returns:**
    /// 
    /// [None] if the global is not already present, otherwise the [`Variable`] that was set before.
    fn set_global(&mut self, name: String, variable: Rc<RefCell<Variable<'ctx>>>) -> Option<Rc<RefCell<Variable<'ctx>>>> {
        self.scope.borrow_mut().set_variable(name, variable)
    }

    /// Check whether the global is defined.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the global to be checked.
    fn contains_global(&self, name: &str) -> bool {
        self.scope.borrow().contains_variable(name)
    }

    /// Set a global's pointer value. This mutates the shared ownership of the global, thus setting the pointer value for all other owners.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the global.
    /// - `pointer` - The [`GlobalValue`] to set.
    /// 
    /// **Panics:**
    /// 
    /// This method is only expected to be used in the compiler when evaluating a global assignment, so the global must already be declared.
    /// In the compiler we know this should be the case because the resolver should have caught it if it is not, if a panic ever occurs it is
    /// because of programmer error in the resolver, this should never panic if the source is valid.
    pub fn set_global_pointer(&mut self, name: &str, global_value: GlobalValue<'ctx>) {
        self.scope.borrow_mut().set_variable_pointer(name, global_value.as_pointer_value())
    }

    /// Get shared ownership of a function pointer.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function to get.
    fn get_function(&self, name: &str) -> Rc<RefCell<Option<FunctionValue<'ctx>>>> {
        self.scope.borrow().get_function(name)
    }

    /// Get a function pointer.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function pointer to get.
    /// 
    /// **Returns:**
    /// 
    /// The [`FunctionValue`] pointer to the function.
    /// 
    /// **Panics:**
    /// 
    /// This method is only expected to be used in the compiler when evaluating a function call, so the function must already be defined and located.
    /// In the compiler we know this should be the case because the resolver should have caught it if it is not the case, if a panic ever occurs it is
    /// because of programmer error in the resolver, this should never panic if the source is valid.
    pub fn get_function_pointer(&self, name: &str) -> FunctionValue<'ctx> {
        self.scope.borrow().get_function_pointer(name)
    }

    /// Add a function to the global scope.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function to add.
    fn add_function(&mut self, name: String) {
        self.scope.borrow_mut().functions.insert(name, Rc::from(RefCell::from(None)));
    }

    /// Set a function's pointer. This mutates the shared ownership of the function pointer, thus changing the value for all other owners.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function to set the pointer of.
    /// - `function_pointer` - The [`FunctionValue`] to set.
    /// 
    /// **Panics:**
    /// 
    /// This method is only expected to be used in the compiler when evaluating a function definition, so the function must already be resolved.
    /// In the compiler we know this should be the case because the resolver should have caught it if it is not the case, if a panic ever occurs it is
    /// because of programmer error in the resolver, this should never panic if the source is valid.
    pub fn set_function_pointer(&mut self, name: &str, function_pointer: FunctionValue<'ctx>) {
        *self.scope.borrow_mut().functions.get_mut(name).expect("FATAL: Function not Declared") = Rc::from(RefCell::from(Some(function_pointer)))
    }

    /// Check whether the function pointer is already scope.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the function to be checked.
    fn contains_function_pointer(&self, name: &str) -> bool {
        self.scope.borrow().contains_function(name)
    }
}

/// Resolve the provided top level [`Stmt`], and retrieve the globals and functions.
/// 
/// **Arguments:**
/// - `top_level` - The top level [`Stmt`] provided by the parser.
/// 
/// **Returns:**
/// 
/// A tuple containing the globals, functions or a vector containing any errors if present.
pub fn resolve<'ctx>(top_level: Vec<Stmt>) -> Result<(Globals<'ctx>, HashMap<String, Function<'ctx>>), Vec<String>> {
    trace_resolver!("Resolving top level");
    let mut resolver = Resolver { globals: Globals::new(), errors: Vec::new(), functions: HashMap::new() };
    let (function_definitions, top_level_stmts): (Vec<Stmt>, Vec<Stmt>) = top_level.into_iter().partition(|stmt| matches!(stmt, Stmt::Function { .. }));

    // Ensure we resolve globals first 
    for stmt in top_level_stmts.into_iter() {
        match stmt {
            Stmt::Expression { ref expr } => resolver.resolve_top_expr(expr),
            _ => panic!("FATAL: Attempting to compile invalid top-level statement, this indicates a programmer error in the parser has caused a catasrophic crash"),
        }

        resolver.globals.add_top_level(stmt)
    }

    // Resolve function prototypes before bodies, this ensures that function bodies can refer to functions declared later in the file
    for stmt in function_definitions.iter() {
        match stmt {
            Stmt::Function { prototype, body: _, is_anon: _ } => resolver.resolve_function_prototype(prototype),
            _ => panic!("FATAL: Attempting to resolve non function as a function, this indicates a programmer error in the parser has caused a catasrophic crash"),
        }
    }

    // Resolve function bodies
    for stmt in function_definitions.into_iter() {
        match stmt {
            Stmt::Function { .. } => resolver.resolve_function_body(stmt),
            _ => panic!("FATAL: Attempting to resolve non function as a function, this indicates a programmer error in the parser has caused a catasrophic crash"),
        }
    }

    // Ensure we have a main function that has been resolved
    if !resolver.functions.contains_key("main") { resolver.errors.push("No main function found".to_string()) }

    if resolver.errors.is_empty() {
        Ok((resolver.globals, resolver.functions))
    } else {
        Err(resolver.errors)
    }
}

/// Contains all state for resolving a file.
struct Resolver<'ctx> {
    globals: Globals<'ctx>,
    errors: Vec<String>,
    functions: HashMap<String, Function<'ctx>>
}

impl<'ctx> Resolver<'ctx> {
    /// Add global declarations to global scope and ensure they are not redefined.
    /// 
    /// **Arguments:**
    /// - `expr` - The top level expression to evaluate.
    /// 
    /// **Panics:**
    /// 
    /// When the resolver tries to resolve a top level statement that is not a variable declaration, this should never happen as long as the parser works correctly.
    /// If this method panics its because of a programmer error in the parser.
    fn resolve_top_expr(&mut self, expr: &Expr) {
        trace_resolver!("Resolving top-level expression: {}", expr);
        match expr {
            Expr::VarDeclar { variable, body } => {
                // Ensure global is unqiue
                if self.globals.contains_global(variable) {
                    self.errors.push(format!("Global: {} is already defined", variable));
                    return;
                }

                // Ensure the global body is valid
                self.resolve_global_body(body);

                let variable_val = Rc::from(RefCell::from(Variable::new()));
                self.globals.set_global(variable.to_string(), variable_val);
            },
            _ => panic!("FATAL: Attempting to resolve invalid top-level statement, this indicates a programmer error in the parser has caused a catasrophic crash")
        }
    }

    /// Ensure an expression within a global body contains only valid expressions and that any variables references are already declared.
    fn resolve_global_body(&mut self, expr: &Expr) {
        trace_resolver!("Resolving global body: {}", expr);
        match expr {
            Expr::VarAssign { variable: _, body: _ } => self.errors.push("Global body must be static".to_string()),
            Expr::Binary { op: _, left, right } => {
                self.resolve_global_body(left);
                self.resolve_global_body(right)
            },
            Expr::Unary { op: _, right } => self.resolve_global_body(right),
            Expr::Call { function_name: _, args: _ } => self.errors.push("Cannot initalise global with a function call".to_string()),
            Expr::Number(_) => {},
            Expr::Variable(_) => self.errors.push("Global body must be static".to_string()),
            Expr::Null => panic!("FATAL: Attempting to resolve null expression, this indicates a programmer error in the parser has caused a catasrophic crash"),
            Expr::VarDeclar { variable: _, body: _ } => panic!("FATAL: Attempting to resolve var declar in a global declaration, this indicates a programmer error in the parser has caused a catasrophic crash"),
        }
    }

    /// Resolve a function prototype, ensuring it hasn't already been declared and adding it to global function scope.
    /// 
    /// **Arguments:**
    /// - `function` - The function statement to resolve.
    fn resolve_function_prototype(&mut self, prototype: &Stmt) {
        let name = match prototype {
            Stmt::Prototype { name, args: _ } => name,
            _ => panic!("FATAL: Attempting to resolve non-prototype statement whilst resolving function, this indicates a programmer error in the parser has caused a catasrophic crash")
        };

        // Ensure function hasn't already been declared
        if self.globals.contains_function_pointer(name) { self.errors.push("Duplicate function: ".to_string() + name) }
        self.globals.add_function(name.clone());
    }

    /// Resolve function declarations and add to map of functions.
    /// 
    /// **Arguments:**
    /// - `state` - The current [ResolverState].
    /// - `expr` - The function expression to evaluate.
    /// 
    /// **Panics:**
    /// 
    /// When the resolver tries to resolve a top level statement that is not a function declaration, this should never happen as long as the parser works correctly.
    /// If this method panics its because of a programmer error in the parser.
    fn resolve_function_body(&mut self, function: Stmt) {
        trace_resolver!("Resolving function: {}", function);
        let (prototype, body) = match function {
            Stmt::Function { prototype, body, is_anon: _ } => (*prototype, body),
            _ => panic!("FATAL: Attempting to resolve non-function statement whilst resolving function, this indicates a programmer error in the parser has caused a catasrophic crash")
        };

        let (name, args) = match prototype {
            Stmt::Prototype { name, args } => (name, args),
            _ => panic!("FATAL: Attempting to resolve non-prototype statement whilst resolving function, this indicates a programmer error in the parser has caused a catasrophic crash")
        };

        // Add function arguments to a scope
        trace_resolver!("Adding function arguments to scope");
        let mut args_scope = Scope::new();
        args_scope.set_parent(self.globals.scope.clone());

        for arg in args {
            trace_resolver!("Adding argument: {}", arg);
            let variable = Rc::from(RefCell::from(Variable::new()));
            if args_scope.set_variable(arg.clone(), variable).is_some() {
                self.errors.push("Duplicate argument: ".to_string() + &arg);
            }
        }

        let args = Rc::from(RefCell::from(args_scope));

        // Run through the body of the function and add variables to scope
        trace_resolver!("Resolving function body");
        let mut scope = Scope::new();
        scope.set_parent(args.clone());
        let scope = Rc::from(RefCell::from(scope));

        let mut resolved_body = Vec::new();
        for stmt in body {
            resolved_body.push(self.resolve_stmt(scope.clone(), stmt));
        }

        let res = self.resolve_returns(&mut resolved_body);
        if !res { self.errors.push("All branches of a function must return".to_string()) }

        let function = Function { args, body: resolved_body, scope };
        self.functions.insert(name, function);
    }

    /// Resolve a statement.
    /// 
    /// **Arguments:**
    /// - `scope` - The scope the statement is in.
    /// - `stmt` - The statement to resolve.
    /// - `errors` - Vector of errors to add to.
    /// 
    /// **Resturns:**
    /// 
    /// The resolved statement.
    fn resolve_stmt(&mut self, scope: Rc<RefCell<Scope<'ctx>>>, stmt: Stmt) -> Statement<'ctx> {
        trace_resolver!("Resolving statement: {}", stmt);
        match stmt {
            Stmt::Expression { expr } => {
                self.resolve_expr(scope, &expr);
                Statement::Expression { expr }
            },
            Stmt::For { start, condition, step, body } => {
                let mut for_scope = Scope::new();
                for_scope.set_parent(scope);
                let for_scope = Rc::from(RefCell::from(for_scope));

                self.resolve_expr(for_scope.clone(), &start);
                self.resolve_expr(for_scope.clone(), &condition);
                self.resolve_expr(for_scope.clone(), &step);

                let mut resolved_body = Vec::new();
                for stmt in body {
                    resolved_body.push(self.resolve_stmt(for_scope.clone(), stmt))
                }

                Statement::For { start, condition, step, body: resolved_body, scope: for_scope }
            },
            Stmt::Conditional { cond, then, otherwise } => {
                self.resolve_expr(scope.clone(), &cond);

                let mut then_scope = Scope::new();
                then_scope.set_parent(scope.clone());
                let then_scope = Rc::from(RefCell::from(then_scope));

                let mut otherwise_scope = Scope::new();
                otherwise_scope.set_parent(scope);
                let otherwise_scope = Rc::from(RefCell::from(otherwise_scope));

                let mut resolved_then = Vec::new();
                for stmt in then {
                    resolved_then.push(self.resolve_stmt(then_scope.clone(), stmt))
                }

                let mut resolved_otherwise = Vec::new();
                for stmt in otherwise {
                    resolved_otherwise.push(self.resolve_stmt(otherwise_scope.clone(), stmt))
                }

                Statement::Conditional { cond, then: resolved_then, otherwise: resolved_otherwise, then_scope, otherwise_scope, returns: false }
            },
            Stmt::Return { body } => {
                self.resolve_expr(scope, &body);
                Statement::Return { body: *body }
            }
            _ => panic!("FATAL: Attempting to resolve function statement in local scope, this indicates a programmer error in the parser has caused a catasrophic crash")
        }
    }

    /// Resolve an expression.
    /// 
    /// **Arguments:**
    /// - `scope` - The scope the expression is in.
    /// - `expr` - The expression to resolve.
    /// - `errors` - Vector of errors to add to.
    fn resolve_expr(&mut self, scope: Rc<RefCell<Scope<'ctx>>>, expr: &Expr) {
        trace_resolver!("Resolving expression: {}", expr);
        match expr {
            Expr::VarDeclar { variable, body } => {
                self.resolve_expr(scope.clone(), body);
                let variable_val = Rc::from(RefCell::from(Variable::new()));
                scope.borrow_mut().set_variable(variable.to_string(), variable_val);
            },
            Expr::VarAssign { variable, body } => {
                self.resolve_variable(scope.clone(), variable);
                self.resolve_expr(scope, body);
            },
            Expr::Binary { op: _, left, right } => {
                self.resolve_expr(scope.clone(), left);
                self.resolve_expr(scope, right);
            },
            Expr::Unary { op: _, right } => self.resolve_expr(scope, right),
            Expr::Call { function_name, args } => {
                // Set the local to point to the global function
                if !self.globals.contains_function_pointer(function_name) {
                    self.errors.push(format!("Function: '{}' is not declared", function_name))
                } else {
                    let function = self.globals.get_function(function_name);
                    scope.borrow_mut().add_function(function_name.to_string(), function);
                }

                for arg in args {
                    self.resolve_expr(scope.clone(), arg)
                } 
            },
            Expr::Number(_) => {},
            Expr::Variable(name) => self.resolve_variable(scope, name),
            // TODO: Put out a void type when types are added
            Expr::Null => {},
        }
    }

    /// Ensure the variable has been declared somewhere and point the variables scope to that location.
    /// 
    /// **Arguments:**
    /// - `scope` - The scope the variable is in.
    /// - `name` - The name of the variable.
    /// - `errors` - Vector of errors to add to.
    fn resolve_variable(&mut self, scope: Rc<RefCell<Scope>>, name: &String) {
        trace_resolver!("Resolving variable: {}", name);

        // If the variable has been declared already in the local scope, nothing needs to be done
        if scope.borrow_mut().contains_variable(name) { return; }

        // Move up scopes, looking for the variable
        let mut higher_scope = scope.borrow().get_parent();
        while let Some(cur_scope) = higher_scope {
            if cur_scope.borrow().contains_variable(name) {
                scope.borrow_mut().set_up_value(name.to_string(), cur_scope.borrow().get_variable(name));
                return;
            }

            higher_scope = cur_scope.borrow().parent.clone();
        }

        // The variable was not found anywhere
        self.errors.push("Could not find variable: ".to_string() + name)
    }

    /// Ensure all return statements in a function are valid, returns true if there is a return statement in the body
    fn resolve_returns(&mut self, statements: &mut [Statement]) -> bool {
        // TODO: Ensure if there are multiple returns in a function that their types match
        for (index, stmt) in statements.iter_mut().enumerate() {
            match stmt {
                Statement::Return { .. } => { 
                    if index != statements.len() - 1 { self.errors.push("Unreachable code".to_string())} 
                    return true;
                },
                Statement::Conditional { then, otherwise, returns, .. } => {
                    let mut res = self.resolve_returns(then);
                    res = res && self.resolve_returns(otherwise);

                    if res {
                        *returns = true;
                        if index != statements.len() - 1 { self.errors.push("Unreachable code".to_string()) }
                        return res;
                    }
                },
                Statement::For { body, .. } => {
                    let res = self.resolve_returns(body);

                    if res {
                        if index != statements.len() - 1 { self.errors.push("Unreachable code".to_string()) }
                        return res;
                    }
                },
                _ => {},
            }
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use crate::{parser, resolver::Statement};
    use super::{resolve, Function, Globals};

    fn run<'a>(input: &str) -> (Globals<'a>, HashMap<String, Function<'a>>) {
        let stmts = parser::parse(input).unwrap();
        resolve(stmts).unwrap()
    }

    fn run_err(input: &str) -> Vec<String> {
        let stmts = parser::parse(input).unwrap();
        if let Err(errs) = resolve(stmts) { errs } else { panic!("FATAL: The resolver has successfully resolved incorrect input") }
    }

    #[test]
    fn global_defintion() {
        let (globals, _) = run("global var x = 5; fun main() { return; }");
        assert!(globals.contains_global("x"))
    }

    #[test]
    fn function_definition() {
        let (_ , functions) = run("fun main() { return; }");
        assert!(functions.contains_key("main"))
    }

    #[test]
    fn use_global_definition() {
        let (_, functions) = run("global var x = 5; fun main() { x; return; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().contains_variable("x"))
    }

    #[test]
    fn use_global_definition_return() {
        let (_, functions) = run("global var x = 5; fun main() { return x; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().contains_variable("x"))
    }

    #[test]
    fn undeclared_variable() {
        let err = run_err("fun main() { var x = y; return; }");
        assert_eq!(vec!["Could not find variable: y"], err)
    }

    #[test]
    fn variable_use_before_declar() {
        let err = run_err("fun main() { x; var x = 1; return; }");
        assert_eq!(vec!["Could not find variable: x"], err)
    }

    #[test]
    fn variable_use_in_declaration() {
        let err = run_err("fun main() { var x = x + 1; return; }");
        assert_eq!(vec!["Could not find variable: x"], err)
    }

    #[test]
    fn variable_use_after_declar() {
        let (_, functions) = run("fun main() { var x = 1; x; return; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().contains_variable("x"))
    }

    #[test]
    fn variable_redeclar() {
        let _ = run("fun main() { var x = 1; var x = 2; return; }");
    }

    #[test]
    fn global_redeclar() {
        let err = run_err("global var x = 1; global var x = 2; fun main() { return; }");
        assert_eq!(vec!["Global: x is already defined"], err);
    }

    #[test]
    fn arg() {
        let (_, functions) = run("fun main(x) { return; }");
        let function = functions.get("main").unwrap();
        assert!(function.args.borrow().contains_variable("x"))
    }

    #[test]
    fn duplicate_arg() {
        let err = run_err("fun main(x, x) {return; }");
        assert_eq!(vec!["Duplicate argument: x"], err)
    }

    #[test]
    fn if_statement() {
        let (_, functions) = run("fun main() { var y = 1; if (y) { var x = y + 1; x; } return; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().contains_variable("y"));

        let conditional = function.body.get(1).unwrap();
        assert!(matches!(conditional, Statement::Conditional { .. }));

        if let Statement::Conditional { then_scope, otherwise_scope, .. } = conditional {
            assert!(then_scope.borrow().contains_variable("x"));
            assert!(then_scope.borrow().contains_variable("y"));
            assert!(otherwise_scope.borrow().variables.is_empty());
        }
    }

    #[test]
    fn for_statement() {
        let (_, functions) = run("fun main() { for (var x = 1; x < 3; x = x + 1) { var z = 2; z; } return; }");
        let function = functions.get("main").unwrap();

        let for_statement = function.body.first().unwrap();
        assert!(matches!(for_statement, Statement::For { start: _, condition: _, step: _, body: _, scope: _ }));

        if let Statement::For { start: _, condition: _, step: _, body: _, scope } = for_statement {
            assert!(scope.borrow().contains_variable("x"));
            assert!(scope.borrow().contains_variable("z"));
        }
    }

    #[test]
    fn for_initialiser_statement() {
        let (_, functions) = run("fun main() { var y = 1; for (var x = y + 1; x < 3; x = x + 1) { var z = 2; z; } return; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().contains_variable("y"));

        let for_statement = function.body.get(1).unwrap();
        assert!(matches!(for_statement, Statement::For { start: _, condition: _, step: _, body: _, scope: _ }));

        if let Statement::For { start: _, condition: _, step: _, body: _, scope } = for_statement {
            assert!(scope.borrow().contains_variable("y"));
            assert!(scope.borrow().contains_variable("x"));
            assert!(scope.borrow().contains_variable("z"));
        }
    }

    #[test]
    fn global_call_val() {
        let err = run_err("global var x = main(); fun main() { return; }");
        assert_eq!(vec!["Cannot initalise global with a function call"], err)
    }

    #[test]
    fn global_undeclared_val() {
        let err = run_err("global var x = y; fun main() { return; }");
        assert_eq!(vec!["Global body must be static"], err)
    }

    #[test]
    fn global_variable_val() {
        let err = run_err("global var y = 1; global var x = y + 1; fun main() { return; }");
        assert_eq!(vec!["Global body must be static"], err)
    }

    #[test]
    fn function_already_defined() {
        let err = run_err("fun main() { return; } fun main() { return; }");
        assert_eq!(vec!["Duplicate function: main"], err)
    }

    #[test]
    fn function_call_non_existent() {
        let err = run_err("fun main() { test(); return; }");
        assert_eq!(vec!["Function: 'test' is not declared"], err)
    }

    #[test]
    fn function_call() {
        let (_, functions) = run("fun test() { return; } fun main() { test(); return; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().contains_function("test"));
    }

    #[test]
    fn recursive_function_call() {
        let (_, functions) = run("fun main() { main(); return; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().contains_function("main"));
    }

    #[test]
    fn no_return() {
        let err = run_err("fun main() {}");
        assert_eq!(vec!["All branches of a function must return"], err)
    }

    #[test]
    fn multiple_return() {
        let _ = run("fun main() { if (1 < 2) { return 1; } else { return 2; } }");
    }

    #[test]
    fn multiple_return_following_return() {
        let err = run_err("fun main() { if (1 < 2) { return 1; } else { return 2; } return 1; }");
        assert_eq!(vec!["Unreachable code"], err)
    }

    #[test]
    fn multiple_return_following_stmt() {
        let err = run_err("fun main() { if (1 < 2) { return 1; } else { return 2; } var x = 1; }");
        assert_eq!(vec!["Unreachable code"], err)
    }

    #[test]
    fn one_branch_return_following_stmt() {
        let err = run_err("fun main() { if (1 < 2) { return 1; } var x = 1; }");
        assert_eq!(vec!["All branches of a function must return"], err)
    }

    #[test]
    fn one_branch_return_following_return() {
        let _ = run("fun main() { if (1 < 2) { return 1; } else { 1; } return; }");
    }

    #[test]
    fn one_branch_return() {
        let err = run_err("fun main() { if (1 < 2) { return 1; } }");
        assert_eq!(vec!["All branches of a function must return"], err)
    }

    // TODO: When nested bodies are added, test them
}