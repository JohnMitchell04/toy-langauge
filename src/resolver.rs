use std::{cell::RefCell, collections::HashMap, rc::Rc};
use inkwell::values::PointerValue;
use crate::{parser::{Expr, Stmt}, trace};

#[derive(Clone)]
// TOOD: Add type info
/// Variable type that holds information about a scopes location in logical scope and its LLVM [PointerValue].
/// 
/// A `scope_location` value of [None] indicates the variable is defined in the local scope, otherwise it points to the scope where the variable is declared.
/// 
/// The `pointer_value` is not filled in the resolver but the compiler adds this information to point to the LLVM value when producing IR.
pub struct Variable<'a> {
    scope_location: Option<Rc<RefCell<Scope<'a>>>>,
    pointer_value: Option<PointerValue<'a>>
}

/// A scope in the program, containing information about variables declared within it and a parent scope if one exists
pub struct Scope<'a> {
    pub variables: HashMap<String, Variable<'a>>,
    pub parent: Option<Rc<RefCell<Scope<'a>>>>,
}

impl<'a> Scope<'a> {
    pub fn new() -> Self {
        Scope { variables: HashMap::new(), parent: None }
    }
}

/// A resolved [Stmt], this differs in that we now have resolved the scopes of the variables referred to in the [Stmt].
pub enum Statement<'a> {
    Conditional {
        cond: Expr,
        then: Vec<Statement<'a>>,
        otherwise: Vec<Statement<'a>>,
        then_scope: Rc<RefCell<Scope<'a>>>,
        otherwise_scope: Rc<RefCell<Scope<'a>>>,
    },
    For {
        var_name: String,
        start: Expr,
        condition: Expr,
        step: Expr,
        body: Vec<Statement<'a>>,
        scope: Rc<RefCell<Scope<'a>>>,
    },
    Expression {
        expr: Expr,
    }
}

/// A function in the program, contains information about variable scope and all statements contained within it.
pub struct Function<'a> {
    name: String,
    args: Rc<RefCell<Scope<'a>>>,
    body: Vec<Statement<'a>>,
    scope: Rc<RefCell<Scope<'a>>>,
}

/// Resolve the provided top level [`Stmt`], and retrieve the globals, top level [`Statement`] and [`Function`].
/// 
/// **Arguments:**
/// - `top_level` - The top level [`Stmt`] provided by the parser.
/// 
/// **Returns:**
/// A tuple containing the globals, top level statements and functions in that order.
pub fn resolve<'a>(top_level: Vec<Stmt>) -> Result<(Rc<RefCell<Scope<'a>>>, Vec<Stmt>, HashMap<String, Function<'a>>), Vec<String>> {
    trace!("Resolving program");
    let mut globals = Scope::new();
    let mut functions = HashMap::new();
    let mut errors = Vec::new();

    let (function_definitions, top_level_stmts): (Vec<Stmt>, Vec<Stmt>) = top_level.into_iter().partition(|stmt| matches!(stmt, Stmt::Function { .. }));

    let top_level = top_level_stmts.clone();

    // Ensure we resolve globals first 
    for stmt in top_level_stmts.into_iter() {
        match stmt {
            Stmt::Expression { expr } => resolve_top_expr(&mut globals, expr, &mut errors),
            _ => panic!("FATAL: Attempting to compile invalid top-level statement, this indicates the parser has failed catasrophically"),
        }
    }
    let globals = Rc::from(RefCell::from(globals));

    // Resolve functions
    for stmt in function_definitions.into_iter() {
        match stmt {
            Stmt::Function { .. } => resolve_function(&mut functions, globals.clone(), stmt, &mut errors),
            _ => panic!("FATAL: Attempting to resolve non function as a function, this indicates the parser has failed catasrophically"),
        }
    }

    if errors.is_empty() {
        Ok((globals, top_level, functions))
    } else {
        Err(errors)
    }
}

/// Resolve some top level global declaration expression and add to globals scope.
fn resolve_top_expr(globals: &mut Scope, expr: Expr, errors: &mut Vec<String>) {
    trace!("Resolving top-level expression");
    match expr {
        Expr::VarDeclar { variable, body: _ } => {
            if globals.variables.get(&variable).is_some() { errors.push(format!("Global: {} is already defined", variable)); return; }
            let variable_val = Variable { scope_location: None, pointer_value: None};
            globals.variables.insert(variable, variable_val);
        },
        _ => panic!("FATAL: Attempting to resolve invalid top-level statement, this indicates the parser has failed catasrophically")
    }
}

/// Resolve some function and add to map of functions.
fn resolve_function<'a>(functions: &mut HashMap<String, Function<'a>>, globals: Rc<RefCell<Scope<'a>>>, function: Stmt, errors: &mut Vec<String>) {
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
    args_scope.parent = Some(globals);
    for arg in args {
        let variable = Variable { scope_location: None, pointer_value: None };
        args_scope.variables.insert(arg, variable);
    }
    let args = Rc::from(RefCell::from(args_scope));

    // Run through the body of the function and add variables to scope
    let mut scope = Scope::new();
    scope.parent = Some(args.clone());
    let scope = Rc::from(RefCell::from(scope));

    let mut resolved_body = Vec::new();
    for stmt in body {
        resolved_body.push(resolve_stmt(scope.clone(), stmt, errors));
    }

    let function = Function { name: name.clone(), args, body: resolved_body, scope };
    functions.insert(name, function);
}

/// Resolve a statement.
fn resolve_stmt<'a>(scope: Rc<RefCell<Scope>>, stmt: Stmt, errors: &mut Vec<String>) -> Statement<'a> {
    trace!("Resolving statement");
    match stmt {
        Stmt::Expression { expr } => {
            resolve_expr(scope, &expr, errors);
            Statement::Expression { expr }
        },
        Stmt::For { var_name, start, condition, step, body } => {
            let mut scope = Scope::new();
            let variable = Variable { scope_location: None, pointer_value: None };
            scope.variables.insert(var_name.clone(), variable);
            let scope = Rc::from(RefCell::from(scope));

            resolve_expr(scope.clone(), &start, errors);
            resolve_expr(scope.clone(), &condition, errors);
            resolve_expr(scope.clone(), &step, errors);

            let mut resolved_body = Vec::new();
            for stmt in body {
                resolved_body.push(resolve_stmt(scope.clone(), stmt, errors))
            }

            Statement::For { var_name, start, condition, step, body: resolved_body, scope }
        },
        Stmt::Conditional { cond, then, otherwise } => {
            resolve_expr(scope, &cond, errors);

            let then_scope = Rc::from(RefCell::from(Scope::new()));
            let otherwise_scope = Rc::from(RefCell::from(Scope::new()));

            let mut resolved_then = Vec::new();
            for stmt in then {
                resolved_then.push(resolve_stmt(then_scope.clone(), stmt, errors))
            }

            let mut resolved_otherwise = Vec::new();
            for stmt in otherwise {
                resolved_otherwise.push(resolve_stmt(otherwise_scope.clone(), stmt, errors))
            }

            Statement::Conditional { cond, then: resolved_then, otherwise: resolved_otherwise, then_scope, otherwise_scope }
        },
        _ => panic!("FATAL: Attempting to resolve function statement in local scope, this indicates the parser has failed catasrophically")
    }
}

/// Resolve an expression.
fn resolve_expr(scope: Rc<RefCell<Scope>>, expr: &Expr, errors: &mut Vec<String>) {
    trace!("Resolving expression");
    match expr {
        Expr::VarDeclar { variable, body } => {
            let variable_val = Variable { scope_location: None, pointer_value: None };
            scope.borrow_mut().variables.insert(variable.to_string(), variable_val);
            resolve_expr(scope, body, errors)
        },
        Expr::VarAssign { variable, body } => {
            check_variable(scope.clone(), variable, errors);
            resolve_expr(scope, body, errors);
        },
        Expr::Binary { op: _, left, right } => {
            resolve_expr(scope.clone(), left, errors);
            resolve_expr(scope, right, errors);
        },
        Expr::Unary { op: _, right } => resolve_expr(scope, right, errors),
        Expr::Call { fn_name: _, args } => for arg in args { resolve_expr(scope.clone(), arg, errors) },
        Expr::Number(_) => {},
        Expr::Variable(name) => check_variable(scope, name, errors),
        Expr::Null => panic!("FATAL: Attempting to resolve null expression, this indicates the parser has failed catasrophically")
    }
}

/// Ensure the variable has been declared somewhere
fn check_variable(scope: Rc<RefCell<Scope>>, name: &String, errors: &mut Vec<String>) {
    trace!("Checking variable: {}", name);

    // If the variable has been declared already in the local scope, nothing needs to be done
    if scope.borrow_mut().variables.get(name).is_some() { return; }

    // Move up scopes, looking for the variable
    let mut cur_scope = scope.borrow().parent.clone();
    while cur_scope.is_some() {
        if let Some(up_scope) = cur_scope.clone().unwrap().borrow_mut().variables.get(name) {
            if up_scope.scope_location.is_some() {
                scope.borrow_mut().variables.insert(name.to_string(), up_scope.clone());
            } else {
                let variable = Variable { scope_location: cur_scope.clone(), pointer_value: None };
                scope.borrow_mut().variables.insert(name.to_string(), variable);
            }

            return;
        }

        cur_scope = cur_scope.unwrap().borrow().parent.clone();
    }

    // The variable was not found anywhere
    errors.push("Error: Could not find variable: ".to_string() + &name)
}

// TODO: Write some tests
// x = x + 1
// x = (2 + 2) * x
// x + 3 + x = 5