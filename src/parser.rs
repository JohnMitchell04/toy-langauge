use std::{fmt::Display, iter::Peekable};
use itertools::Itertools;

use crate::{lexer::{LexResult, Lexer, Token}, trace};

macro_rules! match_no_error {
    ($self:ident, $token:pat, $str:tt) => {
        match $self.peek() {
            Ok($token) => { _ = $self.next() },
            Ok(_) => {
                trace!("Error: {}", $str);
                $self.errors.push(String::from($str))
            },
            Err(ref err) => {
                trace!("Error: {}", err);
                let message = err.error_message(); 
                $self.errors.push(message);
            },
        }
    };
}

macro_rules! err_advance_safe {
    ($self:ident, $message:expr, $($token:pat),*) => {
        {
            // Advance to next safe point
            loop {
                let token = $self.peek();
                if token.is_err() {
                    _ = $self.next();
                } else if matches!(token.as_ref().unwrap(), Token::EOF | $($token)|*) {
                    break
                } else {
                    _ = $self.next()
                }
            }

            if cfg!(debug_assertions) {
                println!("TRACE: ERROR: {}", $message);
            }

            // Add error to list of errors
            $self.errors.push($message);
        }
    };
}

macro_rules! err_add_shorthand {
    ($err:ident, $self:ident) => {
        let message = $err.error_message(); $self.errors.push(message);
    };
}

#[derive(Debug, Clone, PartialEq)]
/// Some code that resolves to a value.
pub enum Expr {
    Binary {
        op: char,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Unary {
        op: char,
        right: Box<Expr>
    },
    Call {
        fn_name: String,
        args: Vec<Expr>,
    },
    Number(f64),
    Variable(String),
    VarDeclar {
        variable: String,
        body: Box<Expr>,
    },
    VarAssign {
        variable: String,
        body: Box<Expr>,
    },
    Null,
}

// TODO: Improve display
impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Binary { op, left, right } => write!(f, "Binary: {} {} {}", left.as_ref(), op, right.as_ref()),
            Self::Unary { op, right } => write!(f, "Unary: {} {}", op, right.as_ref()),
            Self::Call { fn_name, args } => write!(f, "Call: <fn({}) {}>", args.iter().join(","), fn_name),
            Self::Number(num) => write!(f, "Number: {}", num),
            Self::Variable(ident) => write!(f, "Variable: {}", ident),
            Self::VarDeclar { variable, body } => write!(f, "Declaration: {} = {}", variable, body),
            Self::VarAssign { variable, body } => write!(f, "Assignment: {} = {}", variable, body),
            Self::Null => write!(f, "NULL"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
/// Generally some piece of code that does something.
pub enum Stmt {
    Conditional {
        cond: Expr,
        then: Vec<Stmt>,
        otherwise: Vec<Stmt>,
    },
    For {
        start: Expr,
        condition: Expr,
        step: Expr,
        body: Vec<Stmt>,
    },
    Prototype {
        name: String,
        args: Vec<String>,
    },
    Function {
        prototype: Box<Stmt>,
        body: Vec<Stmt>,
        is_anon: bool,
    },
    Expression {
        expr: Expr
    }
}

// TODO: Improve display
impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Conditional { cond, then, otherwise } => write!(f, "If: {} then: {}\nelse: {}", cond, then.iter().join(",\n"), otherwise.iter().join(",\n")),
            Self::For { start, condition, step, body } => write!(f, "For: {}; {}; {}:\n{}", start, condition, step, body.iter().join(",\n")),
            Self::Prototype { name, args } => write!(f, "<fn({}) {}>", args.iter().join(","), name),
            Self::Function { prototype, body, is_anon: _ } => {
                let body = if !body.is_empty() { body.iter().join(",\n") } else { "none".to_string() };
                write!(f, "{}:\n{}", prototype, body)
            },
            Self::Expression { expr } => write!(f, "{}", expr),
        }
    }
}

// TODO: Convert errors to an actual error type and include locational information
pub struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
    errors: Vec<String>,
}

impl<'a> Parser<'a> {
    /// Create a new Parser with the given input.
    /// 
    /// The parser will also create and run a lexer that will process the input.
    pub fn new(input: &'a str) -> Self {
        let lexer = Lexer::new(input).peekable();

        Parser { lexer, errors: Vec::new() }
    }

    // TODO: Maybe return an Rc<[Stmt]> and Rc<[String]>/Rc<[Str]> as we only need the data to be readable
    /// Parse the given input, will return a vector of top level [`Stmt`].
    /// 
    /// **Start** ::= <[Function](Self::parse_function)>
    pub fn parse(&mut self) -> Result<Vec<Stmt>, Vec<String>> {
        trace!("Starting parse");
        let mut top_level = Vec::new();

        while let Ok(token) = self.peek() {
            if *token == Token::EOF { break }

            top_level.push(self.parse_top_level());
        }

        if !self.errors.is_empty() { Err(self.errors.clone()) } else { Ok(top_level) }
    }

    fn peek(&mut self) -> &LexResult {
        self.lexer.peek().unwrap()
    }

    fn next(&mut self) -> LexResult {
        self.lexer.next().unwrap()
    }

    /// Parse a top level statement, this can be a global declaration or a function declaration.
    /// 
    /// **Top-level** ::= <[Global](Self::parse_global)> | <[Extern](Self::parse_extern)> | <[Function](Self::parse_function)>
    fn parse_top_level(&mut self) -> Stmt {
        trace!("Parsing top level statemnt");
        match self.peek() {
            Ok(Token::Global) => self.parse_global(),
            Ok(Token::Extern) => self.parse_extern(),
            Ok(Token::Fun) => self.parse_function(),
            Ok(_) => { 
                self.errors.push(String::from("Statement is not a valid top-level statement"));
                while !matches!(self.peek(), Ok(Token::Global) | Ok(Token::Extern) | Ok(Token::Fun) | Ok(Token::EOF)) { _ = self.next(); }
                Stmt::Expression { expr: Expr::Null }
            },
            Err(ref err) => { err_add_shorthand!(err, self); Stmt::Expression { expr: Expr::Null } },
        }
    }

    /// Parse a global statement
    /// 
    /// **Global** ::= 'global' <[Var](Self::parse_var_stmt)>
    fn parse_global(&mut self) -> Stmt {
        trace!("Parsing global expression");
        _ = self.next();

        self.parse_var_stmt()
    } 

    /// Parse an external function.
    /// 
    /// **Extern** ::= 'extern' <[Prototype](Self::parse_prototype)>
    fn parse_extern(&mut self) -> Stmt {
        trace!("Parsing external");
        _ = self.next();

        let prototype = Box::new(self.parse_prototype());
        Stmt::Function { prototype, body: vec![], is_anon: false}
    }

    /// Parse a function and return a function statement.
    /// 
    /// **Function** ::= 'fun' <[Prototype](Self::parse_prototype)> <[Body](Self::parse_body)>
    fn parse_function(&mut self) -> Stmt {
        trace!("Parsing function definition");

        match_no_error!(self, Token::Fun, "Expected 'fun' keyword before function declaration");

        let prototype = Box::new(self.parse_prototype());
        let body = self.parse_body();

        Stmt::Function { prototype, body, is_anon: false }
    }

    // TODO: Extend to operator function declarations and add return types
    /// Parse a function prototype.
    /// 
    /// **Prototype** ::= <[Ident](Token::Ident)> '(' <[Ident](Token::Ident)>,* ')'
    fn parse_prototype(&mut self) -> Stmt {
        trace!("Parsing prototype");
        let name = match self.peek() {
            Ok(Token::Ident(_)) => self.next().unwrap().take_name(),
            Ok(_) => { self.errors.push("Expected function identifier".to_string()); "".to_string() },
            Err(ref err) => { err_add_shorthand!(err, self); "".to_string() },
        };

        match_no_error!(self, Token::LParen, "Expected '(' before argument list");

        let mut args = Vec::new();
        while let Ok(token) = self.peek() {
            if *token == Token::RParen { break }

            match self.peek() {
                Ok(Token::Ident(_)) => { args.push(self.next().unwrap().take_name()) },
                Ok(_) => err_advance_safe!(self, "Expected argument identifier".to_string(), Token::Comma, Token::RParen, Token::LBrace),
                Err(ref err) => { let message = String::from(err.message) + &err.section; err_advance_safe!(self, message, Token::Comma, Token::RParen, Token::LBrace) },
            }

            match self.peek() {
                Ok(Token::Comma) => { _ = self.next(); },
                Ok(Token::RParen) => break,
                Ok(Token::LBrace) => break,
                Ok(Token::EOF) => break,
                Ok(_) => self.errors.push("Expected comma after identifier".to_string()),
                Err(ref err) => { err_add_shorthand!(err, self); _ = self.next() },
            }
        }

        match_no_error!(self, Token::RParen, "Expected ')' after argument list");

        Stmt::Prototype { name, args }
    }

    /// Parse a function or statement body.
    /// 
    /// **Body** ::= '{' <[Statement](Self::parse_stmt)>* '}'
    fn parse_body(&mut self) -> Vec<Stmt> {
        trace!("Parsing body");
    
        match_no_error!(self, Token::LBrace, "Expected '{' before body");

        let mut stmts = Vec::new();
        while let Ok(node) = self.peek() {
            if *node == Token::RBrace || *node == Token::EOF { break }
            stmts.push(self.parse_stmt());
        }

        match_no_error!(self, Token::RBrace, "Expected '}' after body");

        stmts
    }

    // TODO: Allow body statements i.e. code enclosed in { } to produce a new scope
    /// Parse a statement.
    /// 
    /// **Statement** ::=
    ///   <[ExpressionStatement](Self::parse_expr_stmt)>
    /// | <[Conditional](Self::parse_conditional_stmt)>
    /// | <[For](Self::parse_for_stmt)>
    /// | <[Var](Self::parse_var_stmt)>
    fn parse_stmt(&mut self) -> Stmt {
        trace!("Parsing statement");
        match self.peek() {
            Ok(Token::If) => self.parse_conditional_stmt(),
            Ok(Token::For) => self.parse_for_stmt(),
            Ok(Token::Var) => self.parse_var_stmt(),
            Ok(_) => self.parse_expr_stmt(),
            Err(ref err) => {
                let message = err.error_message();
                err_advance_safe!(self, message, Token::Semicolon);
                Stmt::Expression { expr: Expr::Null }
            },
        }
    }

    /// Parse an expression statement.
    /// 
    /// **ExpressionStatement** ::= [Expression](Self::parse_expr) ';'
    fn parse_expr_stmt(&mut self) -> Stmt {
        trace!("Parsing expression statement");

        let expr = self.parse_expr();

        // Ensure we move to a safe point after a statement
        if let Ok(Token::Semicolon) = self.peek() {
            _ = self.next();
        } else {
            // This is slightly hacky and ideally a better solution should be found, but if an expression had some unmatched parens,
            // we can end in a situation where we don't move to a safe point to continue, which this deals with
            let paren_err = if let Ok(Token::RParen) = self.peek() { true } else { false };

            err_advance_safe!(self, "Expected ';' after expression statement".to_string(), Token::Semicolon, Token::RBrace);

            if paren_err { self.errors.pop(); self.errors.push("Unexpected closing ')'".to_string()); }

            if let Ok(Token::Semicolon) = self.peek() { _ = self.next() }
        }

        Stmt::Expression { expr }
    }

    /// Parse a conditional statement.
    /// 
    /// **Conditional** ::= 'if' '(' <[Expression](Self::parse_expr)> ')' <[Body](Self::parse_body)> ('else' <[Body](Self::parse_body)>)?
    fn parse_conditional_stmt(&mut self) -> Stmt {
        trace!("Parsing conditional expression");
        _ = self.next();

        match_no_error!(self, Token::LParen, "Expected '(' after 'if' keyword");

        let cond = self.parse_expr();

        match_no_error!(self, Token::RParen, "Expected ')' after condition");
        
        let then = self.parse_body();

        let mut otherwise = Vec::new();
        match self.peek() {
            Ok(Token::Else) => {
                _ = self.next();
                otherwise = self.parse_body();
            },
            Ok(Token::LBrace) => {
                self.errors.push(String::from("Expected 'else' keyword before else body"));
                otherwise = self.parse_body();
            }
            Ok(_) => {},
            Err(ref err) => {
                let message = err.error_message();
                err_advance_safe!(self, message, Token::RBrace);
            }
        }

        Stmt::Conditional { cond, then, otherwise }
    }

    // TODO: Make fields optional
    // TODO: Allow the user to use any expression as an initialiser so they can declare a variable or do something to another variable
    /// Parse a for expression.
    /// 
    /// **For** ::= 'for' '(' <[Var](Self::parse_var_stmt)> ';' <[Expression](Self::parse_expr)> ';' <[Expression](Self::parse_expr)> ')' '{' <[Body](Self::parse_body)> '}'
    fn parse_for_stmt(&mut self) -> Stmt {
        trace!("Parsing for expression");
        _ = self.next();

        match_no_error!(self, Token::LParen, "Expected '(' after for");

        let start = match self.parse_var_stmt() {
            Stmt::Expression { expr } => expr,
            _ => panic!("FATAL: This should never happend due to how var statement parsing works"),
        };

        let condition = self.parse_expr();

        match_no_error!(self, Token::Semicolon, "Expected ';' after condition");

        let step = self.parse_expr();

        match_no_error!(self, Token::RParen, "Expected ')' after for definition");
        
        let body = self.parse_body();

        Stmt::For { start, condition, step, body }
    }

    // TODO: Allow multiple assignments and definitions without assignment
    /// Parse a var expression.
    /// 
    /// **Var** ::= 'var' <[Ident](Token::Ident)> '=' <[Expression](Self::parse_expr)> ';'
    fn parse_var_stmt(&mut self) -> Stmt {
        trace!("Parsing var expression");
        _ = self.next();

        let variable = match self.peek() {
            Ok(Token::Ident(_)) => self.next().unwrap().take_name(),
            Ok(_) => { self.errors.push(String::from("Expected variable identifier")); "".to_string() },
            Err(ref err) => { err_add_shorthand!(err, self); "".to_string() },
        };

        match_no_error!(self, Token::Op('='), "Expected '=' after identifier");

        let body = Box::new(self.parse_expr());

        match_no_error!(self, Token::Semicolon, "Expected ';' after assignment");

        Stmt::Expression { expr: Expr::VarDeclar { variable, body } }
    }

    /// Parse any expression, dealing with operator precedences.
    fn parse_expr(&mut self) -> Expr {
        trace!("Parsing expression");
        self.expr_binding(0)
    }

    // TODO: Add support for equality comparisons and logical operators
    /// Recursive expression binding parser.
    fn expr_binding(&mut self, min_binding: u8) -> Expr {
        trace!("Parsing expression binding power: {}", min_binding);
        let mut left = match self.peek() {
            Ok(Token::Number(ref num)) => {
                let num = *num;
                _ = self.next();
                Expr::Number(num)
            },
            Ok(Token::Ident(_)) => self.parse_ident(),
            Ok(Token::LParen) => {
                _ = self.next();
                let left = self.expr_binding(0);
                match_no_error!(self, Token::RParen, "Expected closing ')'");
                left
            },
            Ok(Token::Op(_)) => self.parse_unary(),
            Ok(_) => {
                self.errors.push(String::from("Expected operator, number or ident"));
                Expr::Null
            },
            Err(ref err) => {
                err_add_shorthand!(err, self);
                _ = self.next();
                Expr::Null
            },
        };

        loop {
            let op = match self.peek() {
                Ok(Token::Op(ref op)) => *op,
                Ok(Token::LParen) => '(',
                Ok(Token::EOF) => break,
                Ok(_) => break,
                Err(_) => break,
            };

            if op == '=' {
                _ = self.next();

                let body = Box::new(self.expr_binding(min_binding));

                let name = if let Expr::Variable(name) = left { name } else { self.errors.push(String::from("Attempting to assign to non-variable")); break };
                left = Expr::VarAssign { variable: name, body };
                continue
            }

            if let Some((l_binding, ())) = self.postfix_binding_power(op) {
                if l_binding < min_binding { break }
                _ = self.next();

                left = Expr::Unary { op, right: Box::new(left) };
                continue
            }

            if let Some((l_binding, r_binding)) = self.infix_binding_power(&op) {
                if l_binding < min_binding { break }
                if op == '(' { self.errors.push("Cannot multiply using '('".to_string()) } else { _ = self.next() }
                
                let right = Box::new(self.expr_binding(r_binding));

                left = Expr::Binary { op, left: Box::new(left), right };
                continue
            }

            break
        }
    
        left
    }

    /// Parse a identifier.
    fn parse_ident(&mut self) -> Expr {
        let name = if let Token::Ident(name) = self.next().unwrap() { name } else { panic!("FATAL: Tried to parse non-ident as ident expression, this should never happen") };

        match self.peek() {
            Ok(Token::LParen) => {
                _ = self.next();

                let mut args = Vec::new();
                while let Ok(node) = self.peek() {
                    if *node == Token::RParen { break }

                    args.push(self.parse_expr());

                    match self.peek() {
                        Ok(Token::Comma) => { _ = self.next(); },
                        Ok(Token::RParen) => break,
                        Ok(Token::EOF) => break,
                        Ok(Token::Semicolon) => break,
                        Ok(_) => self.errors.push("Expected comma after identifier".to_string()),
                        Err(ref err) => { err_add_shorthand!(err, self); _ = self.next() },
                    }
                }

                match_no_error!(self, Token::RParen, "Expected ')' after args list");

                Expr::Call { fn_name: name, args }
            },
            Ok(_) => Expr::Variable(name),
            Err(_) => Expr::Variable(name),
        }
    }

    // TODO: Expand to include pre-increment and pre-decrement and logical not
    /// Parse a unary expression.
    fn parse_unary(&mut self) -> Expr {
        trace!("Parsing unary expression");
        let op = if let Token::Op(op) = self.next().unwrap() { 
            op
        } else {
            panic!("FATAL: Tried to parse non-operator as first token in unary expression, this should never happen")
        };


        let ((), r_binding) = if let Some(binding) = self.prefix_binding_power(op) {
            binding
        } else {
            self.errors.push(format!("Bad operator: {}", op));
            return Expr::Null
        };

        let right = Box::new(self.expr_binding(r_binding));
        Expr::Unary { op, right }
    }

    /// Get the binding power of some prefix operator.
    fn prefix_binding_power(&self, op: char) -> Option<((), u8)> {
        trace!("Calculating prefix binding power");
        match op {
            '-' => Some(((), 6)),
            _ => None,
        }
    }

    /// Get the binding power of some infix operator.
    fn infix_binding_power(&self, op: &char) -> Option<(u8, u8)> {
        trace!("Calculating infix binding power");
        match op {
            '(' => Some((0, 0)),
            '=' => Some((0, 1)), // TODO: Investigate with 4 = = 5
            '>' | '<' => Some((2, 3)),
            '+' | '-' => Some((3, 4)),
            '*' | '/' => Some((4, 5)),
            _ => None
        }
    }

    // TODO: Implement arrays
    /// Get the binding power of some postfix operator.
    fn postfix_binding_power(&self, op: char) -> Option<(u8, ())> {
        trace!("Calculating postfix binding power");
        match op {
            _ => None,
        }
    }    
}

// TODO: Add tests for globals and externs
#[cfg(test)]
mod tests {
    use crate::parser::{Expr, Stmt};

    use super::Parser;

    fn parse_no_error(input: &str) -> Vec<Stmt> {
        let mut parser = Parser::new(input);
        parser.parse().unwrap()
    }

    fn parse_error(input: &str) -> Vec<String> {
        let mut parser = Parser::new(input);
        if let Err(errs) = parser.parse() { errs } else { panic!("FATAL: The parser successfully parsed incorrect input") }
    }

    fn create_function(args: Vec<String>, body: Vec<Stmt>) -> Stmt {
        Stmt::Function { 
            prototype: Box::new(Stmt::Prototype { 
                name: "test".to_string(), 
                args,
            }),
            body, 
            is_anon: false 
        }
    }

    #[test]
    fn empty_func() {
        let res = parse_no_error("fun test() {}");
        assert_eq!(create_function(vec![], vec![]), res[0])
    }

    #[test]
    fn func_arg() {
        let res = parse_no_error("fun test(x, y, z) {}");
        assert_eq!(create_function(vec!["x".to_string(), "y".to_string(), "z".to_string()], vec![]), res[0])
    }

    #[test]
    fn func_body() {
        let res = parse_no_error("fun test() { 4 + 5; }");
        assert_eq!(create_function(vec![], vec![Stmt::Expression { expr: Expr::Binary { op: '+', left: Box::new(Expr::Number(4f64)), right: Box::new(Expr::Number(5f64)) } }]), res[0])
    }

    #[test]
    fn func_multiple_body() {
        let res = parse_no_error("fun test() { 4 + 5; 5 - 6; }");
        assert_eq!(
            create_function(vec![], vec![
                Stmt::Expression { expr: Expr::Binary { op: '+', left: Box::new(Expr::Number(4f64)), right: Box::new(Expr::Number(5f64)) } },
                Stmt::Expression { expr: Expr::Binary { op: '-', left: Box::new(Expr::Number(5f64)), right: Box::new(Expr::Number(6f64)) } }    
            ]),
            res[0]
        )
    }

    #[test]
    fn complex_arithmetic() {
        let res = parse_no_error("fun test() { 4 + 5 * 5 - 6 / ((5 + 6) * 6); }");
        assert_eq!(
            create_function(vec![], vec![
                Stmt::Expression { expr: Expr::Binary {
                    op: '-',
                    left: Box::new(Expr::Binary {
                        op: '+',
                        left: Box::new(Expr::Number(4f64)),
                        right: Box::new(Expr::Binary { op: '*', left: Box::new(Expr::Number(5f64)), right: Box::new(Expr::Number(5f64)) }),
                    }),
                    right: Box::new(Expr::Binary { 
                        op: '/',
                        left: Box::new(Expr::Number(6f64)),
                        right: Box::new(Expr::Binary {
                            op: '*',
                            left: Box::new(Expr::Binary { op: '+', left: Box::new(Expr::Number(5f64)), right: Box::new(Expr::Number(6f64)) }),
                            right: Box::new(Expr::Number(6f64)),        
                        })
                    })
                }}
            ]),
            res[0]
        )
    }

    #[test]
    fn call() {
        let res = parse_no_error("fun test() { function(); }");
        assert_eq!(create_function(vec![], vec![Stmt::Expression { expr: Expr::Call { fn_name: "function".to_string(), args: vec![] } }]), res[0])
    }

    #[test]
    fn call_args() {
        let res = parse_no_error("fun test() { function(x, y, z); }");
        assert_eq!(create_function(vec![], vec![
                Stmt::Expression { expr: Expr::Call { fn_name: "function".to_string(), args: vec![Expr::Variable("x".to_string()), Expr::Variable("y".to_string()), Expr::Variable("z".to_string())] } }
            ]),
            res[0]
        )
    }

    #[test]
    fn var_assignment() {
        let res = parse_no_error("fun test() { var x = 4 + 5; }");
        assert_eq!(
            create_function(vec![], vec![
                Stmt::Expression { expr: Expr::VarDeclar { variable: "x".to_string(), body: Box::new(Expr::Binary { op: '+', left: Box::new(Expr::Number(4f64)), right: Box::new(Expr::Number(5f64)) }) } }
            ]),
            res[0]
        )
    }

    #[test]
    fn if_statement() {
        let res = parse_no_error("fun test() { if (1 < 1) { } }");
        assert_eq!(
            create_function(vec![], vec![
                Stmt::Conditional { cond: Expr::Binary { op: '<', left: Box::new(Expr::Number(1f64)), right: Box::new(Expr::Number(1f64)) }, then: vec![], otherwise: vec![] }
            ]),
            res[0]
        )
    }

    #[test]
    fn for_statement() {
        let res = parse_no_error("fun test() { for (var x = 0; x < 1; x = x + 1) { } }");
        assert_eq!(
            create_function(vec![], vec![
                Stmt::For { 
                    start: Expr::VarDeclar { variable: "x".to_string(), body: Box::new(Expr::Number(0f64)) },
                    condition: Expr::Binary { op: '<', left: Box::new(Expr::Variable("x".to_string())), right: Box::new(Expr::Number(1f64)) },
                    step: Expr::VarAssign {
                        variable: "x".to_string(),
                        body: Box::new(Expr::Binary { op: '+', left: Box::new(Expr::Variable("x".to_string())), right: Box::new(Expr::Number(1f64)) })
                    },
                    body: vec![]
                }
            ]),
            res[0]
        )
    }

    #[test]
    fn assignment() {
        let res = parse_no_error("fun test() { x = 1; }");
        assert_eq!(
            create_function(vec![], vec![
                Stmt::Expression { expr: Expr::VarAssign { variable: "x".to_string(), body: Box::new(Expr::Number(1f64)) } }
            ]),
            res[0]
        )
    }

    #[test]
    fn multiple_assignment() {
        let res = parse_no_error("fun test() { x = 1 + y = 2; }");
        assert_eq!(
            create_function(vec![], vec![
                Stmt::Expression { 
                    expr: Expr::VarAssign {
                        variable: "x".to_string(), 
                        body: Box::new(Expr::Binary {
                            op: '+',
                            left: Box::new(Expr::Number(1f64)),
                            right: Box::new(Expr::VarAssign {
                                variable: "y".to_string(),
                                body: Box::new(Expr::Number(2f64))
                            })
                        })
                    }
                }
            ]),
            res[0]
        )
    }

    #[test]
    fn global_declar() {
        let res = parse_no_error("global var x = 5;");
        assert_eq!(vec![Stmt::Expression { expr: Expr::VarDeclar { variable: "x".to_string(), body: Box::new(Expr::Number(5f64)) } }], res);
    }

    #[test]
    fn unary_expr() {
        let res = parse_no_error("fun test() { -5; }");
        assert_eq!(create_function(vec![], vec![Stmt::Expression { expr: Expr::Unary { op: '-', right: Box::new(Expr::Number(5f64)) } }]), res[0])
    }

    #[test]
    fn var_assignment_no_ident() {
        let output = parse_error("fun test() { var = 4 + 5; }");
        assert_eq!(vec!["Expected variable identifier"], output)
    }

    #[test]
    fn var_assignment_no_equal() {
        let output = parse_error("fun test() { var x 4 + 5; }");
        assert_eq!(vec!["Expected '=' after identifier"], output)
    }

    #[test]
    fn var_assignment_no_body() {
        let output = parse_error("fun test() { var x = ; }");
        assert_eq!(vec!["Expected operator, number or ident"], output)
    }

    #[test]
    fn var_assignment_no_end() {
        let output = parse_error("fun test() { var x = 4 + 5 }");
        assert_eq!(vec!["Expected ';' after assignment"], output)
    }

    #[test]
    fn var_assignment_no_ident_no_equal() {
        let output = parse_error("fun test() { var 4 + 5; }");
        assert_eq!(vec!["Expected variable identifier", "Expected '=' after identifier"], output)
    }

    // TODO: when we add null initialisation this should succeed
    #[test]
    fn var_assignment_no_equal_no_body() {
        let output = parse_error("fun test() { var x; }");
        assert_eq!(vec!["Expected '=' after identifier", "Expected operator, number or ident"], output)
    }

    #[test]
    fn var_assignment_no_body_no_end() {
        let output = parse_error("fun test() { var x = }");
        assert_eq!(vec!["Expected operator, number or ident", "Expected ';' after assignment"], output)
    }

    #[test]
    fn var_assignment_nothing() {
        let output = parse_error("fun test() { var ; }");
        assert_eq!(vec!["Expected variable identifier", "Expected '=' after identifier", "Expected operator, number or ident"], output)
    }

    #[test]
    fn var_assignment_no_end_follow() {
        let output = parse_error("fun test() { var x = 4 + 5 var y = 5 + 4; }");
        assert_eq!(vec!["Expected ';' after assignment"], output)
    }

    #[test]
    fn if_statement_no_lparen() {
        let output = parse_error("fun test() { if 0 < 1) { } }");
        assert_eq!(vec!["Expected '(' after 'if' keyword"], output)
    }

    #[test]
    fn if_statement_no_rparen() {
        let output = parse_error("fun test() { if (0 < 1 { } }");
        assert_eq!(vec!["Expected ')' after condition"], output)
    }

    #[test]
    fn if_statement_no_cond() {
        let output = parse_error("fun test() { if () { } }");
        assert_eq!(vec!["Expected operator, number or ident"], output)
    }

    #[test]
    fn if_statement_no_parens() {
        let output = parse_error("fun test() { if  { } }");
        assert_eq!(vec!["Expected '(' after 'if' keyword", "Expected operator, number or ident", "Expected ')' after condition"], output)
    }

    #[test]
    fn if_statement_no_parens_but_cond() {
        let output = parse_error("fun test() { if 1 < 1 { } }");
        assert_eq!(vec!["Expected '(' after 'if' keyword", "Expected ')' after condition"], output)
    }

    #[test]
    fn func_no_end() {
        let output = parse_error("fun test( { 5 + 6; }");
        assert_eq!(vec!["Expected argument identifier", "Expected ')' after argument list"], output)
    }

    #[test]
    fn func_no_end_args() {
        let output = parse_error("fun test(x, y, z { 5 + 6; }");
        assert_eq!(vec!["Expected ')' after argument list"], output)
    }

    #[test]
    fn func_no_end_args_plus_another_error() {
        let output = parse_error("fun test(x, y, z { 5 + 6 }");
        assert_eq!(vec!["Expected ')' after argument list", "Expected ';' after expression statement"], output)
    }

    #[test]
    fn func_args_no_comma() {
        let output = parse_error("fun test(x y z) { 5 + 6; }");
        assert_eq!(vec!["Expected comma after identifier", "Expected comma after identifier"], output)
    }

    #[test]
    fn func_args_accidental_comma() {
        let output = parse_error("fun test(, x, y, z) { 5 + 6; }");
        assert_eq!(vec!["Expected argument identifier"], output)
    }

    #[test]
    fn func_args_double_comma() {
        let output = parse_error("fun test(x, , y, z) { 5 + 6; }");
        assert_eq!(vec!["Expected argument identifier"], output)
    }

    #[test]
    fn func_no_body() {
        let output = parse_error("fun test() ");
        assert_eq!(vec!["Expected '{' before body", "Expected '}' after body"], output)
    }

    #[test]
    fn func_no_body_but_stmt() {
        let output = parse_error("fun test() 5 + 6; ");
        assert_eq!(vec!["Expected '{' before body", "Expected '}' after body"], output)
    }

    #[test]
    fn func_no_end_body() {
        let output = parse_error("fun test() { 5 + 6; ");
        assert_eq!(vec!["Expected '}' after body"], output)
    }

    #[test]
    fn func_no_start_body_no_arg_end() {
        let output = parse_error("fun test(  5 + 6; ");
        assert_eq!(vec!["Expected argument identifier", "Expected ')' after argument list", "Expected '{' before body", "Expected '}' after body"], output)
    }

    #[test]
    fn func_incorrect_arg_type() {
        let output = parse_error("fun test(5 + 6;) {}");
        assert_eq!(vec!["Expected argument identifier"], output)
    }

    #[test]
    fn func_no_keyword() {
        let output = parse_error("test() { }");
        assert_eq!(vec!["Statement is not a valid top-level statement"], output)
    }

    #[test]
    fn func_no_identifier() {
        let output = parse_error("fun () { }");
        assert_eq!(vec!["Expected function identifier"], output)
    }

    #[test]
    fn func_no_parens() {
        let output = parse_error("fun test { }");
        assert_eq!(vec!["Expected '(' before argument list", "Expected argument identifier", "Expected ')' after argument list"], output)
    }

    #[test]
    fn func_no_parens_no_body() {
        let output = parse_error("fun test ");
        assert_eq!(vec!["Expected '(' before argument list", "Expected argument identifier", "Expected ')' after argument list", "Expected '{' before body", "Expected '}' after body"], output)
    }

    #[test]
    fn func_nothing() {
        let output = parse_error("fun ");
        assert_eq!(vec!["Expected function identifier", "Expected '(' before argument list", "Expected argument identifier", "Expected ')' after argument list", "Expected '{' before body", "Expected '}' after body"], output)
    }

    #[test]
    fn func_ident_invalid_token() {
        let output = parse_error("fun test(a b!) { }");
        assert_eq!(vec!["Invalid identifier: b!"], output)
    }

    // TODO: Add failure tests for for statements

    #[test]
    fn invalid_expr_keyword() {
        let output = parse_error("fun test() { 4 + fun * 5 - 6; }");
        assert_eq!(vec!["Expected operator, number or ident", "Expected ';' after expression statement"], output)
    }

    #[test]
    fn invalid_expr_ident() {
        let output = parse_error("fun test() { 4 + b! * 5 - 6 / ((5 + 6) * 6); }");
        assert_eq!(vec!["Invalid identifier: b!"], output)
    }

    #[test]
    fn invalid_expr_mult() {
        let output = parse_error("fun test() { 5(6); }");
        assert_eq!(vec!["Cannot multiply using '('"], output)
    }

    #[test]
    fn invalid_expr_random_paren() {
        let output = parse_error("fun test() { 4 + 5((5 + 6); }");
        assert_eq!(vec!["Cannot multiply using '('", "Expected closing ')'",], output)
    }

    #[test]
    fn invalid_expr_missing_paren_end() {
        let output = parse_error("fun test() { ((5 + 6) * 6; }");
        assert_eq!(vec!["Expected closing ')'"], output)
    }

    #[test]
    fn invalid_expr_missing_paren_midway() {
        let output = parse_error("fun test() { ((5 + 6 * 6); }");
        assert_eq!(vec!["Expected closing ')'"], output)
    }

    #[test]
    fn invalid_expr_extra_paren() {
        let output = parse_error("fun test() { (5 + 6) * 6); }");
        assert_eq!(vec!["Unexpected closing ')'"], output)
    }

    #[test]
    fn invalid_expr_extra_paren_simple() {
        let output = parse_error("fun test() { (5 + 6)); }");
        assert_eq!(vec!["Unexpected closing ')'"], output)
    }

    #[test]
    fn invalid_assignment_target() {
        let output = parse_error("fun test() { 1 = 2; }");
        assert_eq!(vec!["Attempting to assign to non-variable"], output)
    }
}