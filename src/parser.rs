use std::{fmt::Display, iter::Peekable};
use itertools::Itertools;

use crate::{lexer::{LexResult, Lexer, Token}, trace};

// TODO: This macro is likely temporary whilst error handling is decided
macro_rules! match_error_stmt {
    ($self:ident, $token:pat, $str:tt) => {
        match $self.peek() {
            Ok($token) => { _ = $self.next() },
            Ok(_) => return $self.err_recover_stmt($str),
            Err(err) => {
                let message = err.message;
                return $self.err_recover_stmt(message)
            },
        }
    };
}

macro_rules! match_error_expr {
    ($self:ident, $token:pat, $str:tt) => {
        match $self.peek() {
            Ok($token) => { _ = $self.next() },
            Ok(_) => return $self.err_recover_expr($str),
            Err(err) => {
                let message = err.message;
                return $self.err_recover_expr(message)
            },
        }
    };
}

macro_rules! match_no_error {
    ($self:ident, $token:pat, $str:tt) => {
        match $self.peek() {
            Ok($token) => { _ = $self.next() },
            Ok(_) => {
                trace!("Error: {}", $str);
                $self.errors.push($str)
            },
            Err(err) => {
                trace!("Error: {}", err);
                let message = err.message;
                $self.errors.push(message)
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

// TODO: Split VarAssign into VarDeclare and VarAssign, and ensure our expressions actually allow assignment

#[derive(Debug, PartialEq)]
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
    VarAssign {
        variable: String,
        body: Box<Expr>,
    },
    Null,
}

// TODO Improve display
impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Binary { op, left, right } => write!(f, "Binary: {} {} {}", left.as_ref(), op, right.as_ref()),
            Self::Unary { op, right } => write!(f, "Unary: {} {}", op, right.as_ref()),
            Self::Call { fn_name, args } => write!(f, "Call: <fn({}) {}>", args.iter().join(","), fn_name),
            Self::Number(num) => write!(f, "Number: {}", num),
            Self::Variable(ident) => write!(f, "Variable: {}", ident),
            Self::VarAssign { variable, body } => write!(f, "Assignment: {} = {}", variable, body),
            Self::Null => write!(f, "NULL"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Stmt {
    Conditional {
        cond: Expr,
        then: Vec<Stmt>,
        otherwise: Vec<Stmt>,
    },
    For {
        var_name: String,
        start: Expr,
        condition: Expr,
        step: Expr,
        body: Vec<Stmt>,
    },
    Prototype {
        name: String,
        args: Vec<String>,
        is_op: bool,
        prec: usize,
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

// TODO Improve display
impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Conditional { cond, then, otherwise } => write!(f, "If: {} then: {}\nelse: {}", cond, then.iter().join(",\n"), otherwise.iter().join(",\n")),
            Self::For { var_name, start, condition, step, body } => write!(f, "For: {} = {}; {}; {}:\n{}", var_name, start, condition, step, body.iter().join(",\n")),
            Self::Prototype { name, args, is_op: _, prec: _ } => write!(f, "<fn({}) {}>", args.iter().join(","), name),
            Self::Function { prototype, body, is_anon: _ } => {
                let body = if !body.is_empty() { body.iter().join(",\n") } else { "none".to_string() };
                write!(f, "{}:\n{}", prototype, body)
            },
            Self::Expression { expr } => write!(f, "{}", expr),
        }
    }
}

pub struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
    errors: Vec<&'static str>,
    panic_mode: bool
}

// TODO: Test this parser with malformed input and fine tune the error handling process
impl<'a> Parser<'a> {
    /// Create a new Parser with the given input.
    /// 
    /// The parser will also create and run a lexer that will process the input.
    pub fn new(input: &'a str) -> Self {
        let lexer = Lexer::new(input).into_iter().peekable();

        Parser { lexer, errors: Vec::new(), panic_mode: false }
    }

    /// Parse the given input, will return an anonymous [`Function`] containing the parsed source or an error message.
    /// 
    /// **Start** ::= <[FunctionDefinition](Self::parse_fun_def)>
    pub fn parse(&mut self) -> Result<Vec<Stmt>, Vec<&'static str>> {
        trace!("Starting parse");
        // TODO: Right now we will only accept a single top level function definition, eventually this will be expanded to allow more functions, globals and links to other files
        let body = self.parse_fun_def();

        // TODO: This is only temporary for whilst we only allow one function def
        if let Ok(token) = self.peek() {
            if *token != Token::EOF { self.errors.push("Unexpected token after parsed expression") }
        }

        if !self.errors.is_empty() { Err(self.errors.clone()) } else { Ok(vec![body]) }
    }

    /// Get the errors accrued whilst parsing.
    pub fn get_errors(&self) -> &[&'static str] {
        &self.errors
    }

    // TODO: Improve with locational information.
    // TODO: Complex functions that use this can continue to try and parse themselves instead of returning to their parent.
    /// Add an error to the parser and advance to the next safe location, this ensures we try and collect the maximal number of errors possible.
    fn err_recover_stmt(&mut self, message: &'static str) -> Stmt {
        self.panic_mode = true;

        // Advance to next safe point
        loop {
            let token = self.peek();
            if token.is_err() {
                _ = self.next();
            } else if matches!(token.as_ref().unwrap(), Token::Semicolon | Token::LParen | Token::RParen | Token::LBrace | Token::RBrace | Token::EOF) {
                _ = self.next();
                break
            } else {
                _ = self.next()
            }
        }

        if cfg!(debug_assertions) {
            println!("TRACE: ERROR: {}", message);
        }

        // Add error to list of errors
        self.errors.push(message);
        Stmt::Expression { expr: Expr::Null }
    }

    fn err_recover_expr(&mut self, message: &'static str) -> Expr {
        self.panic_mode = true;

        // Advance to next safe point
        loop {
            let token = self.peek();
            if token.is_err() {
                _ = self.next();
            } else if matches!(token.as_ref().unwrap(), Token::Semicolon | Token::LParen | Token::RParen | Token::LBrace | Token::RBrace | Token::EOF) {
                _ = self.next();
                break
            } else {
                _ = self.next()
            }
        }

        if cfg!(debug_assertions) {
            println!("TRACE: ERROR: {}", message);
        }

        // Add error to list of errors
        self.errors.push(message);
        Expr::Null 
    }

    fn peek(&mut self) -> &LexResult {
        self.lexer.peek().unwrap()
    }

    fn next(&mut self) -> LexResult {
        self.lexer.next().unwrap()
    }

    // TODO: Extend to operator function declarations and add return types
    /// Parse a function prototype.
    /// 
    /// **Prototype** ::= <[Ident](Token::Ident)> '(' <[Ident](Token::Ident)>,* ')'
    fn parse_prototype(&mut self) -> Stmt {
        trace!("Parsing prototype");
        let name = match self.peek() {
            Ok(Token::Ident(_)) => self.next().unwrap().take_name(),
            Ok(_) => { self.errors.push("Expected function identifier"); "".to_string() },
            Err(ref err) => { let message = err.message; self.errors.push(message); "".to_string() },
        };

        match_no_error!(self, Token::LParen, "Expected '(' before argument list");

        let mut args = Vec::new();
        while let Ok(token) = self.peek() {
            if *token == Token::RParen { break }

            match self.peek() {
                Ok(Token::Ident(_)) => { args.push(self.next().unwrap().take_name()) },
                Ok(_) => err_advance_safe!(self, "Expected argument identifier", Token::Comma, Token::RParen, Token::LBrace),
                Err(err) => {let message = err.message; err_advance_safe!(self, message, Token::Comma, Token::RParen, Token::LBrace) },
            }

            match self.peek() {
                Ok(Token::Comma) => { _ = self.next(); },
                Ok(Token::RParen) => break,
                Ok(Token::LBrace) => break,
                Ok(Token::EOF) => break,
                Ok(_) => self.errors.push("Expected comma after identifier"),
                Err(err) => { let message = err.message; self.errors.push(message) },
            }
        }

        match_no_error!(self, Token::RParen, "Expected ')' after argument list");

        Stmt::Prototype { name, args, is_op: false, prec: 0 }
    }

    // TODO: This is not used right now, implement when globals are added
    /// Parse an external.
    /// 
    /// **Extern** ::= 'extern' <[Prototype](Self::parse_prototype)>
    fn parse_extern(&mut self) -> Stmt {
        trace!("Parsing external");

        // TODO: Parse extern keyword

        let prototype = Box::new(self.parse_prototype());
        Stmt::Function { prototype, body: vec![], is_anon: false}
    }

    /// Parse a function definition and return a function object.
    /// 
    /// **FunctionDefinition** ::= 'fun' <[Prototype](Self::parse_prototype)> <[Body](Self::parse_body)>
    fn parse_fun_def(&mut self) -> Stmt {
        trace!("Parsing function definition");

        match_no_error!(self, Token::Fun, "Expected 'fun' keyword before function declaration");

        let prototype = Box::new(self.parse_prototype());
        let body = self.parse_body();

        Stmt::Function { prototype, body, is_anon: false }
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
            Err(err) => {
                let message = err.message;
                self.err_recover_stmt(message)
            },
        }
    }

    /// Parse an expression statement.
    /// 
    /// **ExpressionStatement** ::= [Expression](Self::parse_expr) ';'
    fn parse_expr_stmt(&mut self) -> Stmt {
        trace!("Parsing expression statement");

        let expr = self.parse_expr();
        match_error_stmt!(self, Token::Semicolon, "Expected ';' after expression statement");
        Stmt::Expression { expr }
    }

    /// Parse a conditional statement.
    /// 
    /// **Conditional** ::= 'if' '(' <[Expression](Self::parse_expr)> ')' <[Body](Self::parse_body)> ('else' <[Body](Self::parse_body)>)?
    fn parse_conditional_stmt(&mut self) -> Stmt {
        trace!("Parsing conditional expression");
        _ = self.next();

        match_error_stmt!(self, Token::LParen, "Expect '(' after 'if' keyword");

        let cond = self.parse_expr();

        match_error_stmt!(self, Token::RParen, "Expect ')' after condtion");
        
        let then = self.parse_body();

        let mut otherwise = Vec::new();
        match self.peek() {
            Ok(Token::Else) => {
                _ = self.next();
                otherwise = self.parse_body();
            },
            Ok(_) => {},
            Err(err) => {
                let message = err.message;
                return self.err_recover_stmt(message)
            }
        }

        Stmt::Conditional { cond, then, otherwise }
    }

    // TODO: Implement optional useage of each for field
    /// Parse a for expression.
    /// 
    /// **For** ::= 'for' '(' <[Ident](Token::Ident)> '=' <[Expression](Self::parse_expr)> ';' <[Expression](Self::parse_expr)> ';' <[Expression](Self::parse_expr)> ')' '{' <[Body](Self::parse_body)> '}'
    fn parse_for_stmt(&mut self) -> Stmt {
        trace!("Parsing for expression");
        _ = self.next();

        match_error_stmt!(self, Token::LBrace, "Expected '(' after for");

        let var_name = match self.next() {
            Ok(Token::Ident(ident)) => ident,
            Ok(_) => return self.err_recover_stmt("Expected identifier in initialiser"),
            Err(err) => return self.err_recover_stmt(err.message),
        };

        match_error_stmt!(self, Token::Op('='), "Expected '=' after identifier");

        let start = self.parse_expr();

        match_error_stmt!(self, Token::Semicolon, "Expected ';' after initialiser");

        let condition = self.parse_expr();

        match_error_stmt!(self, Token::Semicolon, "Expected ';' after condition");

        let step = self.parse_expr();

        match_error_stmt!(self, Token::RParen, "Expected ')' after for definition");
        
        let body = self.parse_body();

        Stmt::For { var_name, start, condition, step, body }
    }

    // TODO: Allow multiple assignments and definitions without assignment
    /// Parse a var expression.
    /// 
    /// **Var** ::= 'var' <[Ident](Token::Ident)> '=' <[Expression](Self::parse_expr)> ';'
    fn parse_var_stmt(&mut self) -> Stmt {
        trace!("Parsing var expression");
        _ = self.next();

        let variable = match self.next() {
            Ok(Token::Ident(id)) => id,
            Ok(_) => return self.err_recover_stmt("Expected identifier"),
            Err(err) => return self.err_recover_stmt(err.message),
        };

        match_error_stmt!(self, Token::Op('='), "Expected '=' after identifier");

        let body = Box::new(self.parse_expr());

        match_error_stmt!(self, Token::Semicolon, "Expected ';' after assignment");

        Stmt::Expression { expr: Expr::VarAssign { variable, body } }
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
        let mut left = match self.next() {
            Ok(Token::Number(num)) => Expr::Number(num),
            Ok(Token::Ident(name)) => self.parse_ident(name),
            Ok(Token::LParen) => {
                let left = self.expr_binding(0);
                match_error_expr!(self, Token::RParen, "Expected closing ')'");
                left
            }
            Ok(Token::Op(op)) => {
                let ((), r_binding) = self.prefix_binding_power(op);
                let right = Box::new(self.expr_binding(r_binding));
                Expr::Unary { op, right }
            },
            Ok(_) => return self.err_recover_expr("Expected operator or number"),
            Err(err) => return self.err_recover_expr(err.message),
        };

        loop {
            let op = match self.peek() {
                Ok(Token::Op(op)) => op,
                Ok(Token::EOF) => break,
                Ok(_) => return left,
                Err(err) => {
                    let message = err.message;
                    return self.err_recover_expr(message)
                },
            }.clone();

            if let Some((l_binding, ())) = self.postfix_binding_power(op) {
                if l_binding < min_binding { break }
                _ = self.next();

                left = Expr::Unary { op, right: Box::new(left) };
                continue
            }

            if let Some((l_binding, r_binding)) = self.infix_binding_power(&op) {
                if l_binding < min_binding { break }

                _ = self.next();
                let right = Box::new(self.expr_binding(r_binding));

                left = Expr::Binary { op, left: Box::new(left), right };
                continue
            }

            break
        }
    
        left
    }

    /// Get the binding power of some prefix operator.
    fn prefix_binding_power(&self, op: char) -> ((), u8) {
        match op {
            '-' => ((), 5),
            // TODO: Probably don't panic here
            _ => panic!("Bad operator"),
        }
    }

    /// Get the binding power of some infix operator.
    fn infix_binding_power(&self, op: &char) -> Option<(u8, u8)> {
        trace!("Calculting binding power");
        match op {
            '+' | '-' => Some((1, 2)),
            '*' | '/' => Some((3, 4)),
            _ => None
        }
    }

    // TODO: Implement arrays
    /// Get the binding power of some postfix operator.
    fn postfix_binding_power(&self, op: char) -> Option<(u8, ())> {
        match op {
            _ => return None,
        }
    }

    /// Parse a identifier 
    fn parse_ident(&mut self, name: String) -> Expr {
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
                        Ok(_) => return self.err_recover_expr("Expected ',' or ')' after expression"),
                        Err(err) => {
                            let message = err.message;
                            return self.err_recover_expr(message)
                        },
                    }
                }

                match_error_expr!(self, Token::RParen, "Expected ')' after args list");

                Expr::Call { fn_name: name, args }
            },
            Ok(_) => Expr::Variable(name),
            Err(err) => {
                let message = err.message;
                self.err_recover_expr(message)
            },
        }
    }    
}

#[cfg(test)]
mod tests {
    use crate::parser::{Expr, Stmt};

    use super::Parser;

    fn parse_no_error(input: &str) -> Vec<Stmt> {
        let mut parser = Parser::new(input);
        parser.parse().unwrap()
    }

    fn parse_error(input: &str) -> Vec<&'static str> {
        let mut parser = Parser::new(input);
        _ = parser.parse();
        parser.get_errors().iter().map(|&s| s).collect()
    }

    // TODO: Right now all tests have a single top level function in line with the current grammar, when the grammar is expanded add new tests
    // TODO: Write some functions or macros to clean up this boiler plate
    #[test]
    fn empty_func() {
        let res = parse_no_error("fun test() {}");
        assert_eq!(
            Stmt::Function { 
                prototype: Box::new(Stmt::Prototype { 
                    name: "test".to_string(), 
                    args: vec![], 
                    is_op: false, 
                    prec: 0 
                }),
                body: vec![], 
                is_anon: false 
            }, 
            res[0]
        )
    }

    #[test]
    fn func_arg() {
        let res = parse_no_error("fun test(x, y, z) {}");
        assert_eq!(
            Stmt::Function {
                prototype: Box::new(Stmt::Prototype { 
                    name: "test".to_string(),
                    args: vec!["x".to_string(), "y".to_string(), "z".to_string()],
                    is_op: false,
                    prec: 0
                }), 
                body: vec![],
                is_anon: false
            },
            res[0]
        )
    }

    #[test]
    fn func_body() {
        let res = parse_no_error("fun test() { 4 + 5; }");
        assert_eq!(
            Stmt::Function {
                prototype: Box::new(Stmt::Prototype {
                    name: "test".to_string(),
                    args: vec![],
                    is_op: false,
                    prec: 0
                }),
                body: vec![Stmt::Expression { expr: Expr::Binary { op: '+', left: Box::new(Expr::Number(4f64)), right: Box::new(Expr::Number(5f64)) } }], 
                is_anon: false
            },
            res[0]
        )
    }

    #[test]
    fn func_multiple_body() {
        let res = parse_no_error("fun test() { 4 + 5; 5 - 6; }");
        assert_eq!(
            Stmt::Function {
                prototype: Box::new(Stmt::Prototype {
                    name: "test".to_string(),
                    args: vec![],
                    is_op: false,
                    prec: 0
                }), 
                body: vec![
                    Stmt::Expression { expr: Expr::Binary { op: '+', left: Box::new(Expr::Number(4f64)), right: Box::new(Expr::Number(5f64)) } },
                    Stmt::Expression { expr: Expr::Binary { op: '-', left: Box::new(Expr::Number(5f64)), right: Box::new(Expr::Number(6f64)) } }    
                ], 
                is_anon: false
            },
            res[0]
        )
    }

    #[test]
    fn complex_arithmetic() {
        let res = parse_no_error("fun test() { 4 + 5 * 5 - 6 / ((5 + 6) * 6); }");
        assert_eq!(
            Stmt::Function {
                prototype: Box::new(Stmt::Prototype {
                    name: "test".to_string(),
                    args: vec![],
                    is_op: false,
                    prec: 0
                }), 
                body: vec![
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
                ], 
                is_anon: false
            },
            res[0]
        )
    }

    #[test]
    fn call() {
        let res = parse_no_error("fun test() { function(); }");
        assert_eq!(
            Stmt::Function {
                prototype: Box::new(Stmt::Prototype {
                    name: "test".to_string(),
                    args: vec![],
                    is_op: false,
                    prec: 0
                }),
                body: vec![Stmt::Expression { expr: Expr::Call { fn_name: "function".to_string(), args: vec![] } }],
                is_anon: false,
            }, 
            res[0]
        )
    }

    #[test]
    fn call_args() {
        let res = parse_no_error("fun test() { function(x, y, z); }");
        assert_eq!(
            Stmt::Function {
                prototype: Box::new(Stmt::Prototype {
                    name: "test".to_string(),
                    args: vec![],
                    is_op: false,
                    prec: 0
                }),
                body: vec![Stmt::Expression { expr: Expr::Call { fn_name: "function".to_string(), args: vec![Expr::Variable("x".to_string()), Expr::Variable("y".to_string()), Expr::Variable("z".to_string())] } }],
                is_anon: false,
            }, 
            res[0]
        )
    }

    #[test]
    fn var_assignment() {
        let res = parse_no_error("fun test() { var x = 4 + 5; }");
        assert_eq!(
            Stmt::Function {
                prototype: Box::new(Stmt::Prototype {
                    name: "test".to_string(),
                    args: vec![],
                    is_op: false,
                    prec: 0
                }),
                body: vec![
                    Stmt::Expression { expr: Expr::VarAssign { variable: "x".to_string(), body: Box::new(Expr::Binary { op: '+', left: Box::new(Expr::Number(4f64)), right: Box::new(Expr::Number(5f64)) }) } }
                ], 
                is_anon: false
            },
            res[0]
        )
    }

    #[test]
    fn func_no_end() {
        let output = parse_error("fun test( { 5 + 6; }");
        assert_eq!(vec!["Expected argument identifier", "Expected ')' after argument list"], output)
    }

    #[test]
    fn func_args_no_end() {
        let output = parse_error("fun test(x, y, z { 5 + 6; }");
        assert_eq!(vec!["Expected ')' after argument list"], output)
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
        assert_eq!(vec!["Expected 'fun' keyword before function declaration"], output)
    }

    #[test]
    fn func_no_identifier() {
        let output = parse_error("fun () { }");
        assert_eq!(vec!["Expected function identifier"], output)
    }
}