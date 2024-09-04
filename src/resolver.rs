use std::{cell::RefCell, collections::HashMap, rc::Rc};
use inkwell::values::PointerValue;
use crate::{parser::{Expr, Stmt}, trace};

// TOOD: Add type info
/// Variable type that holds information about a variables location in logical scope and its LLVM [PointerValue].
/// 
/// A `scope_location` value of [None] indicates the variable is defined in the local scope, otherwise it points to the scope where the variable is declared.
/// 
/// The `pointer_value` is not filled in by the resolver but the compiler adds this information to point to the LLVM value when producing IR.
#[derive(Clone)]
pub struct Variable<'ctx> {
    scope_location: Option<Rc<RefCell<Scope<'ctx>>>>,
    pointer_value: Option<PointerValue<'ctx>>
}

/// A scope in the program, containing information about variables declared within it and a parent scope if one exists.
pub struct Scope<'ctx> {
    variables: HashMap<String, Variable<'ctx>>,
    parent: Option<Rc<RefCell<Scope<'ctx>>>>,
}

impl<'ctx> Scope<'ctx> {
    /// Create a new scope with no variables and no parent.
    pub fn new() -> Self {
        Scope { variables: HashMap::new(), parent: None }
    }

    /// Get the scope's parent.
    ///
    /// **Returns:**
    /// 
    /// The parent if the scope has one, [None] otherwise
    pub fn get_parent(&self) -> Option<Rc<RefCell<Scope<'ctx>>>> {
        self.parent.clone()
    }

    /// Set the scope's parent.
    /// 
    /// **Arguments:**
    /// - `parent` - A reference to the parent.
    pub fn set_parent(&mut self, parent: Rc<RefCell<Scope<'ctx>>>) {
        self.parent = Some(parent)
    }

    /// Get some variable in the scope.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the variable to retrieve.
    /// 
    /// **Returns:**
    /// 
    /// [`None`] if the variable is not present in the scope, otherwise an [`Variable`].
    pub fn get_variable(&self, name: &str) -> Option<&Variable<'ctx>> {
        self.variables.get(name)
    }

    /// Set a variable in the scope.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the variable to set.
    /// - `variable` - The [`Variable`] to set.
    /// 
    /// **Returns:**
    /// 
    /// [None] if the variable is not already present, otherwise the [`Variable`] that was set before.
    pub fn set_variable(&mut self, name: String, variable: Variable<'ctx>) -> Option<Variable<'ctx>> {
        self.variables.insert(name, variable)
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
    },
    For {
        start: Expr,
        condition: Expr,
        step: Expr,
        body: Vec<Statement<'ctx>>,
        scope: Rc<RefCell<Scope<'ctx>>>,
    },
    Expression {
        expr: Expr,
    }
}

/// A function in the program, contains information about variable scope and all statements contained within it.
pub struct Function<'ctx> {
    name: String,
    args: Rc<RefCell<Scope<'ctx>>>,
    body: Vec<Statement<'ctx>>,
    scope: Rc<RefCell<Scope<'ctx>>>,
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
    pub fn set_top_level(&mut self, stmts: Vec<Stmt>) {
        self.stmts = stmts
    }

    /// Get some global.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the global to retrieve.
    /// 
    /// **Returns:**
    /// 
    /// [`None`] if the global is not present, otherwise an [`Variable`].
    pub fn get_global(&self, name: &str) -> Option<Variable<'ctx>> {
        self.scope.borrow().get_variable(name).cloned()
    }

    /// Set a global.
    /// 
    /// **Arguments:**
    /// - `name` - The name of the global to set.
    /// - `variable` - The [`Variable`] to set.
    /// 
    /// **Returns:**
    /// 
    /// [None] if the global is not already present, otherwise the [`Variable`] that was set before.
    pub fn set_global(&mut self, name: String, variable: Variable<'ctx>) -> Option<Variable<'ctx>> {
        self.scope.borrow_mut().set_variable(name, variable)
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
    trace!("Resolving top level");
    let mut resolver = Resolver { functions: HashMap::new(), globals: Globals::new(), errors: Vec::new() };
    let (function_definitions, top_level_stmts): (Vec<Stmt>, Vec<Stmt>) = top_level.into_iter().partition(|stmt| matches!(stmt, Stmt::Function { .. }));

    // Ensure we resolve globals first 
    for stmt in top_level_stmts.iter() {
        match stmt {
            Stmt::Expression { expr } => resolver.resolve_top_expr(expr),
            _ => panic!("FATAL: Attempting to compile invalid top-level statement, this indicates the parser has failed catasrophically"),
        }
    }
    resolver.globals.set_top_level(top_level_stmts);

    // Resolve functions
    for stmt in function_definitions.into_iter() {
        match stmt {
            Stmt::Function { .. } => resolver.resolve_function(stmt),
            _ => panic!("FATAL: Attempting to resolve non function as a function, this indicates the parser has failed catasrophically"),
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
    functions: HashMap<String, Function<'ctx>>,
    globals: Globals<'ctx>,
    errors: Vec<String>,
}

impl<'ctx> Resolver<'ctx> {
    /// Add global declarations to global scope and ensure they are not redefined.
    /// 
    /// **Arguments:**
    /// - `state` - The current [ResolverState].
    /// - `expr` - The top level expression to evaluate.
    /// 
    /// **Panics:**
    /// 
    /// When the resolver tries to resolve a top level statement that is not a variable declaration, this should never happen as long as the parser works correctly.
    fn resolve_top_expr(&mut self, expr: &Expr) {
        trace!("Resolving top-level expression");
        match expr {
            Expr::VarDeclar { variable, body: _ } => {
                if self.globals.get_global(variable).is_some() {
                    self.errors.push(format!("Global: {} is already defined", variable));
                    return;
                }

                let variable_val = Variable { scope_location: None, pointer_value: None};
                self.globals.set_global(variable.to_string(), variable_val);
            },
            _ => panic!("FATAL: Attempting to resolve invalid top-level statement, this indicates the parser has failed catasrophically")
        }
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
    fn resolve_function(&mut self, function: Stmt) {
        trace!("Resolving function");
        let (prototype, body) = match function {
            Stmt::Function { prototype, body, is_anon: _ } => (*prototype, body),
            _ => panic!("FATAL: Attempting to resolve non-function statement whilst resolving function, this indicates the parser has failed catasrophically")
        };

        let (name, args) = match prototype {
            Stmt::Prototype { name, args } => (name, args),
            _ => panic!("FATAL: Attempting to resolve non-prototype statement whilst resolving function, this indicates the parser has failed catasrophically")
        };

        // Add function arguments to a scope
        let mut args_scope = Scope::new();
        args_scope.parent = Some(self.globals.scope.clone());

        for arg in args {
            let variable = Variable { scope_location: None, pointer_value: None };
            if args_scope.set_variable(arg.clone(), variable).is_some() {
                self.errors.push("Duplicate argument: ".to_string() + &arg);
            }
        }
        let args = Rc::from(RefCell::from(args_scope));

        // Run through the body of the function and add variables to scope
        let mut scope = Scope::new();
        scope.parent = Some(args.clone());
        let scope = Rc::from(RefCell::from(scope));

        let mut resolved_body = Vec::new();
        for stmt in body {
            resolved_body.push(self.resolve_stmt(scope.clone(), stmt));
        }

        let function = Function { name: name.clone(), args, body: resolved_body, scope };
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
        trace!("Resolving statement");
        match stmt {
            Stmt::Expression { expr } => {
                self.resolve_expr(scope, &expr);
                Statement::Expression { expr }
            },
            Stmt::For { start, condition, step, body } => {
                let mut for_scope = Scope::new();
                for_scope.parent = Some(scope);
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
                then_scope.parent = Some(scope.clone());
                let then_scope = Rc::from(RefCell::from(then_scope));

                let mut otherwise_scope = Scope::new();
                otherwise_scope.parent = Some(scope);
                let otherwise_scope = Rc::from(RefCell::from(otherwise_scope));

                let mut resolved_then = Vec::new();
                for stmt in then {
                    resolved_then.push(self.resolve_stmt(then_scope.clone(), stmt))
                }

                let mut resolved_otherwise = Vec::new();
                for stmt in otherwise {
                    resolved_otherwise.push(self.resolve_stmt(otherwise_scope.clone(), stmt))
                }

                Statement::Conditional { cond, then: resolved_then, otherwise: resolved_otherwise, then_scope, otherwise_scope }
            },
            _ => panic!("FATAL: Attempting to resolve function statement in local scope, this indicates the parser has failed catasrophically")
        }
    }

    /// Resolve an expression.
    /// 
    /// **Arguments:**
    /// - `scope` - The scope the expression is in.
    /// - `expr` - The expression to resolve.
    /// - `errors` - Vector of errors to add to.
    fn resolve_expr(&mut self, scope: Rc<RefCell<Scope>>, expr: &Expr) {
        trace!("Resolving expression");
        match expr {
            Expr::VarDeclar { variable, body } => {
                self.resolve_expr(scope.clone(), body);
                let variable_val = Variable { scope_location: None, pointer_value: None };
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
            Expr::Call { fn_name: _, args } => for arg in args { self.resolve_expr(scope.clone(), arg) },
            Expr::Number(_) => {},
            Expr::Variable(name) => self.resolve_variable(scope, name),
            Expr::Null => panic!("FATAL: Attempting to resolve null expression, this indicates the parser has failed catasrophically")
        }
    }

    /// Ensure the variable has been declared somewhere and point the variables scope to that location.
    /// 
    /// **Arguments:**
    /// - `scope` - The scope the variable is in.
    /// - `name` - The name of the variable.
    /// - `errors` - Vector of errors to add to.
    fn resolve_variable(&mut self, scope: Rc<RefCell<Scope>>, name: &String) {
        trace!("Checking variable: {}", name);

        // If the variable has been declared already in the local scope, nothing needs to be done
        if scope.borrow_mut().get_variable(name).is_some() { return; }

        // Move up scopes, looking for the variable
        let mut higher_scope = scope.borrow().get_parent();
        while let Some(cur_scope) = higher_scope {
            if let Some(up_scope) = cur_scope.borrow().get_variable(name) {
                if up_scope.scope_location.is_some() {
                    scope.borrow_mut().variables.insert(name.to_string(), up_scope.clone());
                } else {
                    let variable = Variable { scope_location: Some(cur_scope.clone()), pointer_value: None };
                    scope.borrow_mut().variables.insert(name.to_string(), variable);
                }

                return;
            }

            higher_scope = cur_scope.borrow().parent.clone();
        }

        // The variable was not found anywhere
        self.errors.push("Could not find variable: ".to_string() + name)
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
        let (globals, _) = run("global var x = 5; fun main() {}");
        assert!(globals.get_global("x").is_some())
    }

    #[test]
    fn use_global_definition() {
        let (_, functions) = run("global var x = 5; fun main() { x; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().variables.contains_key("x"))
    }

    #[test]
    fn function_definition() {
        let (_, functions) = run("fun main() {}");
        assert!(functions.contains_key("main"))
    }

    #[test]
    fn undeclared_variable() {
        let err = run_err("fun main() { var x = y; }");
        assert_eq!(vec!["Could not find variable: y"], err)
    }

    #[test]
    fn variable_use_before_declar() {
        let err = run_err("fun main() { x; var x = 1; }");
        assert_eq!(vec!["Could not find variable: x"], err)
    }

    #[test]
    fn variable_use_in_declaration() {
        let err = run_err("fun main() { var x = x + 1; }");
        assert_eq!(vec!["Could not find variable: x"], err)
    }

    #[test]
    fn variable_use_after_declar() {
        let (_, functions) = run("fun main() { var x = 1; x; }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().variables.contains_key("x"))
    }

    #[test]
    fn variable_redeclar() {
        let _ = run("fun main() { var x = 1; var x = 2; }");
    }

    #[test]
    fn global_redeclar() {
        let err = run_err("global var x = 1; global var x = 2; fun main() {}");
        assert_eq!(vec!["Global: x is already defined"], err);
    }

    #[test]
    fn arg() {
        let (_, functions) = run("fun main(x) {}");
        let function = functions.get("main").unwrap();
        assert!(function.args.borrow().variables.contains_key("x"))
    }

    #[test]
    fn duplicate_arg() {
        let err = run_err("fun main(x, x) {}");
        assert_eq!(vec!["Duplicate argument: x"], err)
    }

    #[test]
    fn if_statement() {
        let (_, functions) = run("fun main() { var y = 1; if (y) { var x = y + 1; x; }}");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().variables.contains_key("y"));

        let conditional = function.body.last().unwrap();
        assert!(matches!(conditional, Statement::Conditional { cond: _, then: _, otherwise: _, then_scope: _, otherwise_scope: _ }));

        if let Statement::Conditional { cond: _, then: _, otherwise: _, then_scope, otherwise_scope } = conditional {
            assert!(then_scope.borrow().variables.contains_key("x"));
            assert!(then_scope.borrow().variables.contains_key("y"));
            assert!(otherwise_scope.borrow().variables.is_empty());
        }
    }

    #[test]
    fn for_statement() {
        let (_, functions) = run("fun main() { var y = 1; for (var x = y + 1; x < 3; x = x + 1) { var z = 2; z; } }");
        let function = functions.get("main").unwrap();
        assert!(function.scope.borrow().variables.contains_key("y"));

        let for_statement = function.body.last().unwrap();
        assert!(matches!(for_statement, Statement::For { start: _, condition: _, step: _, body: _, scope: _ }));

        if let Statement::For { start: _, condition: _, step: _, body: _, scope } = for_statement {
            assert!(scope.borrow().variables.contains_key("y"));
            assert!(scope.borrow().variables.contains_key("x"));
            assert!(scope.borrow().variables.contains_key("z"));
        }
    }

    // TODO: When nested bodies are added, test them
}