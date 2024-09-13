use std::{error::Error, fmt::Display};
use crate::trace;

macro_rules! trace_lexer {
    ($($arg:tt)*) => {
        if cfg!(debug_assertions) {
            if std::env::var("LEXER_TRACE").is_ok() {
                trace!("LEXER", $($arg)*)
            }
        }
    };
}

/// A token within our grammar.
#[derive(Debug, Clone, PartialEq)]
#[allow(clippy::upper_case_acronyms)]
pub enum Token {
    // Single character structure tokens
    Comma, Semicolon, LParen, RParen, LBrace, RBrace, LBrack, RBrack,

    // Keywords
    Fun, Extern, For, If, Else, Unary, Binary, Var, Global, Return,

    // TODO: Maybe add ** and // as raising to powers
    // Operations
    Equal, Plus, Sub, Divide, Greater, PlusPlus, SubSub, PlusEqual, SubEqual, MulEqual, DivideEqual, Exclam,

    // Comparisons
    Star, Less, EqualEqual, LessEqual, GreaterEqual, ExclamEqual,

    // Type keywords
    // Void, Bool, I8, I16, I32, I64, I128, U8, U16, U32, U64, U128, F16, F32, F64, F128,

    // User data
    Ident(String), Number(f64),

    EOF,
}

impl Token {
    pub fn take_name(&mut self) -> String {
        match std::mem::replace(self, Self::EOF) {
            Self::Ident(name) => name,
            _ => panic!("Cannot take variable name"),
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // Single character structure tokens
            Self::Comma => write!(f, ","),
            Self::Semicolon => write!(f, ";"),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::LBrack => write!(f, "["),
            Self::RBrack => write!(f, "]"),

            // Keywords
            Self::Fun => write!(f, "fun"),
            Self::Extern => write!(f, "extern"),
            Self::For => write!(f, "for"),
            Self::If => write!(f, "if"),
            Self::Else => write!(f, "else"),
            Self::Unary => write!(f, "unary"),
            Self::Binary => write!(f, "binary"),
            Self::Var => write!(f, "var"),
            Self::Global => write!(f, "global"),
            Self::Return => write!(f, "return"),

            // Operations
            Self::Equal => write!(f, "="),
            Self::Plus => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Divide => write!(f, "/"),
            Self::Star => write!(f, "*"),
            Self::PlusPlus => write!(f, "++"),
            Self::SubSub => write!(f, "--"),
            Self::PlusEqual => write!(f, "+="),
            Self::SubEqual => write!(f, "-="),
            Self::MulEqual => write!(f, "*="),
            Self::DivideEqual => write!(f, "/="),
            Self::Exclam => write!(f, "!"),

            // Comparisons
            Self::Less => write!(f, "<"),
            Self::Greater => write!(f, ">"),
            Self::EqualEqual => write!(f, "=="),
            Self::LessEqual => write!(f, "<="),
            Self::GreaterEqual => write!(f, ">="),
            Self::ExclamEqual => write!(f, "!="),

            // User data
            Self::Ident(ident) => write!(f, "Identifier: {}", ident),
            Self::Number(num) => write!(f, "Number: {}", &num.to_string()),

            Self::EOF => write!(f, "EOF"),
        }
    }
}

// TODO: The full capability of this error isn't really used, at some point we should add locational information to errors
#[derive(Debug, Clone, PartialEq)]
pub struct LexError {
    pub message: &'static str,
    pub section: String,
    pub col: usize,
    pub line: usize,
}

impl LexError {
    pub fn error_message(&self) -> String {
        String::from(self.message) + ": " + &self.section
    }
}

impl LexError {
    pub fn new(message: &'static str, section: String, col: usize, line: usize) -> LexError {
        LexError { message, section, col, line }
    }
}

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error {}: {}\nOn line: {} column: {}", self.message, self.section, self.line, self.col)
    }
}

impl Error for LexError {}

pub type LexResult<'a> = Result<Token, LexError>;

pub struct Lexer<'a> {
    input: &'a [char],
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer on the given input.
    pub fn new(input: &'a [char]) -> Self {
        Lexer { input, pos: 0, line: 1, col: 1 }
    }

    /// Consume the next character.
    /// 
    /// **Returns:**
    /// 
    /// The next character, or [`None`] if we are at the end of the input.
    fn next_char(&mut self) -> Option<char> {
        if self.pos == self.input.len() {
            None
        } else {
            self.pos += 1;
            self.col += 1;
            Some(self.input[self.pos - 1])
        }
    }

    /// Peek the next character.
    /// 
    /// **Returns:**
    /// 
    /// The next character, or [`None`] if we are at the end of the input.
    fn peek_char(&self) -> Option<char> {
        if self.pos == self.input.len() { None } else { Some(self.input[self.pos]) }
    }

    /// Peek two characters ahead.
    /// 
    /// **Returns:**
    /// 
    /// The character two ahead, or [`None`] if it is as the end of the input.
    fn peek_two_char(&self) -> Option<char> {
        if self.pos + 1 >= self.input.len() { None } else { Some(self.input[self.pos + 1]) }
    }

    /// Check if the given character is a structure character.
    fn is_structure(&self, char: char) -> bool {
        matches!(char, '+' | '-' | '<' | '>' | '=' | '*' | '/' | '(' | ')' | '{' | '}' | '[' | ']' | ',' | ';')
    }

    /// Retrieve the next token
    pub fn next_token(&mut self) -> LexResult {
        self.skip_whitespace();
        let character = self.peek_char();

        let result = match character {
            Some(',') => { _ = self.next_char(); Ok(Token::Comma) },
            Some(';') => { _ = self.next_char(); Ok(Token::Semicolon) },
            Some('(') => { _ = self.next_char(); Ok(Token::LParen) },
            Some(')') => { _ = self.next_char(); Ok(Token::RParen) },
            Some('{') => { _ = self.next_char(); Ok(Token::LBrace) },
            Some('}') => { _ = self.next_char(); Ok(Token::RBrace) },
            Some('[') => { _ = self.next_char(); Ok(Token::LBrack) },
            Some(']') => { _ = self.next_char(); Ok(Token::RBrack) },
            Some('0'..='9') => self.parse_number(),
            Some('a'..='z' | 'A'..='Z' | '_') => self.parse_ident(),
            Some('=') => {
                _ = self.next_char();
                match self.peek_char() {
                    Some('=') => { _ = self.next_char(); Ok(Token::EqualEqual) },
                    _ => Ok(Token::Equal),
                }
            }
            Some('+') => {
                _ = self.next_char();
                match self.peek_char() {
                    Some('=') => { _ = self.next_char(); Ok(Token::PlusEqual) },
                    Some('+') => { _ = self.next_char(); Ok(Token::PlusPlus) },
                    _ => Ok(Token::Plus),
                }
            },
            Some('-') => {
                _ = self.next_char();
                match self.peek_char() {
                    Some('=') => { _ = self.next_char(); Ok(Token::SubEqual) },
                    Some('-') => { _ = self.next_char(); Ok(Token::SubSub) },
                    _ => Ok(Token::Sub),
                }
            },
            Some('*') => {
                _ = self.next_char();
                match self.peek_char() {
                    Some('=') => { _ = self.next_char(); Ok(Token::MulEqual) },
                    _ => Ok(Token::Star),
                }
            },
            Some('/') => {
                _ = self.next_char();
                match self.peek_char() {
                    Some('=') => { _ = self.next_char(); Ok(Token::DivideEqual) },
                    _ => Ok(Token::Divide),
                }
            },
            Some('<') => {
                _ = self.next_char();
                match self.peek_char() {
                    Some('=') => { _ = self.next_char(); Ok(Token::LessEqual) },
                    _ => Ok(Token::Less),
                }
            },
            Some('>') => {
                _ = self.next_char();
                match self.peek_char() {
                    Some('=') => { _ = self.next_char(); Ok(Token::GreaterEqual) },
                    _ => Ok(Token::Greater),
                }
            }
            Some('!') => {
                _ = self.next_char();
                match self.peek_char() {
                    Some('=') => { _ = self.next_char(); Ok(Token::ExclamEqual) },
                    _ => Ok(Token::Exclam),
                }
            },
            Some(_) => { _ = self.next_char(); Err(LexError::new("Unexpected character", self.input[self.pos - 1..self.pos].iter().collect(), self.col - 1, self.line)) },
            None => Ok(Token::EOF),
        };

        #[cfg(debug_assertions)]
        match result {
            Ok(ref token) => trace_lexer!("Produced token: {}", token),
            Err(ref err) => trace_lexer!("Produced token: {}", err)
        }
        
        result
    }

    /// Parse an identifier or keyword.
    /// 
    /// **Ident** ::= [0-9a-zA-Z_]*
    fn parse_ident(&mut self) -> LexResult {
        trace_lexer!("Parsing identifier");
        let start = self.pos;
        let col_start = self.col;

        while let Some(char) = self.peek_char() {
            if char != '_' && !char.is_ascii_alphanumeric() { break; }
            self.next_char();
        }

        let mut invalid = false;
        while let Some(char) = self.peek_char() {
            if char.is_whitespace() || self.is_structure(char) { break }

            self.next_char();
            invalid = true;
        }

        if invalid { return Err(LexError::new("Invalid identifier", self.input[start..self.pos].iter().collect(), col_start, self.line)) }

        // TODO: Accept capitalisation but still create an error, that way we can still try and parse the code but also inform the user
        // Keywords
        match &self.input[start..self.pos] {
            ['f', 'u', 'n'] => Ok(Token::Fun),
            ['e', 'x', 't', 'e', 'r', 'n'] => Ok(Token::Extern),
            ['i', 'f'] => Ok(Token::If),
            ['e', 'l', 's', 'e'] => Ok(Token::Else),
            ['f', 'o', 'r'] => Ok(Token::For),
            ['u', 'n', 'a', 'r', 'y'] => Ok(Token::Unary),
            ['b', 'i', 'n', 'a', 'r', 'y'] => Ok(Token::Binary),
            ['v', 'a', 'r'] => Ok(Token::Var),
            ['g', 'l', 'o', 'b', 'a', 'l'] => Ok(Token::Global),
            ['r', 'e', 't', 'u', 'r', 'n'] => Ok(Token::Return),
            ident => Ok(Token::Ident(ident.iter().collect())),
        }
    }

    /// Parse a number literal.
    /// 
    /// **Number** ::= [0-9a-zA-Z]* (. [])?
    fn parse_number(&mut self) -> LexResult {
        trace_lexer!("Parsing number");
        let start = self.pos;
        let col_start = self.col;

        while let Some(char) = self.peek_char() {
            if char != '.' && !char.is_ascii_hexdigit() { break; }

            self.next_char();
        }

        let mut invalid = false;
        while let Some(char) = self.peek_char() {
            if char.is_whitespace() || self.is_structure(char) { break }

            self.next_char();
            invalid = true;
        }

        if invalid { return Err(LexError::new("Invalid identifier", self.input[start..self.pos].iter().collect(), col_start, self.line)) }

        // TODO: Re-do when the number literal token is re-worked
        let num: String = self.input[start..self.pos].iter().collect();
        if num.chars().any(|char| char.is_ascii_alphabetic() && char != '.'){
            match u32::from_str_radix(&num, 16) {
                Ok(num) => Ok(Token::Number(num as f64)),
                Err(_) => Err(LexError::new("Invalid hex number format", num, col_start, self.line)),
            }
        } else {
            match num.parse() {
                Ok(num) => Ok(Token::Number(num)),
                Err(_) => Err(LexError::new("Invalid number format", num, col_start, self.line)),
            }
        }
    }

    // TODO: skip comments
    /// Skip whitespace characters and comments.
    fn skip_whitespace(&mut self) {
        trace_lexer!("Skipping whitespace");
        while let Some(char) = self.peek_char() {
            if char == '/' {
                if let Some('/') = self.peek_two_char() {
                    loop {
                        let char = self.next_char();
                        if char == Some('\n') || char.is_none() {
                            self.line += 1;
                            self.col = 1;
                            break;
                        }
                    }
                } else {
                    return;
                }
            } else {
                if !char.is_whitespace() { break }
    
                self.next_char();
                if char == '\n' {
                    self.line += 1;
                    self.col = 1;
                }
            }
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = LexResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.next_token())
    }
}

// TODO: Add tests for LBrack and RBrack, add tests for new operations and comparisons
#[cfg(test)]
mod tests {
    use crate::lexer::LexError;
    use super::{LexResult, Lexer, Token};

    fn create_lexer(input: &str) -> Vec<Token> {
        if !input.is_ascii() { panic!("Testing input must be ASCII") }
        let input: Vec<char> = input.chars().collect();
        let lexer = Lexer::new(&input);
        let mut temp: Vec<Token> = lexer.into_iter().take_while(|res| *res.as_ref().unwrap() != Token::EOF).map(|res| res.unwrap()).collect();
        temp.push(Token::EOF);
        temp
    }

    fn create_lexer_res(input: &str) -> LexResult {
        if !input.is_ascii() { panic!("Testing input must be ASCII") }
        let input: Vec<char> = input.chars().collect();
        let mut lexer = Lexer::new(&input);
        lexer.next_token()
    }

    #[test]
    fn comment() {
        let output = create_lexer("// this is a comment");
        assert_eq!(vec![Token::EOF], output)
    }

    #[test]
    fn integer() {
        let output = create_lexer("5");
        assert_eq!(vec![Token::Number(5f64), Token::EOF], output)
    }

    // Re-write tests when number types are added
    #[test]
    fn large_integer() {
        let output = create_lexer("50000000000000000000000");
        assert_eq!(vec![Token::Number(50000000000000000000000f64), Token::EOF], output)
    }

    #[test]
    fn float() {
        let output = create_lexer("5.1");
        assert_eq!(vec![Token::Number(5.1f64), Token::EOF], output)
    }

    #[test]
    fn long_float() {
        let output = create_lexer("5.00000000000000000000001");
        assert_eq!(vec![Token::Number(5.00000000000000000000001f64), Token::EOF], output)
    }

    #[test]
    fn invalid_float() {
        let output = create_lexer_res("5.1.5");
        assert_eq!(Err(LexError::new("Invalid number format", "5.1.5".to_string(), 1, 1)), output)
    }

    #[test]
    fn hex_number() {
        let output = create_lexer("5FA");
        assert_eq!(vec![Token::Number(0x5FA as f64), Token::EOF], output)
    }

    #[test]
    fn invalid_float_hex() {
        let output = create_lexer_res("5.FA");
        assert_eq!(Err(LexError::new("Invalid hex number format", "5.FA".to_string(), 1, 1)), output)
    }

    #[test]
    fn invalid_num_character() {
        let output = create_lexer_res(".");
        assert_eq!(Err(LexError::new("Unexpected character", ".".to_string(), 1, 1)), output)
    }

    #[test]
    fn invalid_character() {
        let output = create_lexer_res("~");
        assert_eq!(Err(LexError::new("Unexpected character", "~".to_string(), 1, 1)), output)
    }

    #[test]
    fn keyword() {
        let output = create_lexer("extern");
        assert_eq!(vec![Token::Extern, Token::EOF], output)
    }

    #[test]
    fn ident() {
        let output = create_lexer("input");
        assert_eq!(vec![Token::Ident("input".to_string()), Token::EOF], output)
    }

    #[test]
    fn invalid_ident() {
        let output = create_lexer_res("tes!t");
        assert_eq!(Err(LexError::new("Invalid identifier", "tes!t".to_string(), 1, 1)), output)
    }

    #[test]
    fn invalid_ident_after() {
        let output = create_lexer_res("b!)");
        assert_eq!(Err(LexError::new("Invalid identifier", "b!".to_string(), 1, 1)), output)
    }

    #[test]
    fn invalid_number() {
        let output = create_lexer_res("5test");
        assert_eq!(Err(LexError::new("Invalid identifier", "5test".to_string(), 1, 1)), output)
    }

    #[test]
    fn numeric_simple() {
        let output = create_lexer("5 + 5");
        assert_eq!(vec![Token::Number(5f64), Token::Plus, Token::Number(5f64), Token::EOF], output)
    }

    #[test]
    fn numeric_complex() {
        let output = create_lexer("(5+5) * 5");
        assert_eq!(vec![Token::LParen, Token::Number(5f64), Token::Plus, Token::Number(5f64), Token::RParen, Token::Star, Token::Number(5f64), Token::EOF], output)
    }

    #[test]
    fn assign_expr() {
        let output = create_lexer("var test = 5;");
        assert_eq!(vec![Token::Var, Token::Ident("test".to_string()), Token::Equal, Token::Number(5f64), Token::Semicolon, Token::EOF], output)
    }

    #[test]
    fn for_loop() {
        let output = create_lexer("for (x = 5; x < 10; x = x + 1) { var test = 5; }");
        assert_eq!(
            vec![
                Token::For, Token::LParen, Token::Ident("x".to_string()), Token::Equal, Token::Number(5f64), Token::Semicolon, Token::Ident("x".to_string()),
                Token::Less, Token::Number(10f64), Token::Semicolon, Token::Ident("x".to_string()), Token::Equal, Token::Ident("x".to_string()),
                Token::Plus, Token::Number(1f64), Token::RParen, Token::LBrace, Token::Var, Token::Ident("test".to_string()), Token::Equal, Token::Number(5f64),
                Token::Semicolon, Token::RBrace, Token::EOF
            ],
            output
        )
    }

    #[test]
    fn func() {
        let output = create_lexer("fun test(x, y, z) {}");
        assert_eq!(
            vec![
                Token::Fun, Token::Ident("test".to_string()), Token::LParen, Token::Ident("x".to_string()), Token::Comma, Token::Ident("y".to_string()),
                Token::Comma, Token::Ident("z".to_string()), Token::RParen, Token::LBrace, Token::RBrace, Token::EOF
            ],
            output
        )
    }

    #[test]
    fn pre_increment() {
        let output = create_lexer("++test");
        assert_eq!(vec![Token::PlusPlus, Token::Ident("test".to_string()), Token::EOF], output)
    }

    #[test]
    fn post_increment() {
        let output = create_lexer("test++");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::PlusPlus, Token::EOF], output)
    }

    #[test]
    fn pre_decrement() {
        let output = create_lexer("--test");
        assert_eq!(vec![Token::SubSub, Token::Ident("test".to_string()), Token::EOF], output)
    }

    #[test]
    fn post_decrement() {
        let output = create_lexer("test--");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::SubSub, Token::EOF], output)
    }

    #[test]
    fn plus_equal() {
        let output = create_lexer("test += 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::PlusEqual, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn sub_equal() {
        let output = create_lexer("test -= 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::SubEqual, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn mul_equal() {
        let output = create_lexer("test *= 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::MulEqual, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn divide_equal() {
        let output = create_lexer("test /= 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::DivideEqual, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn exclam() {
        let output = create_lexer("!test");
        assert_eq!(vec![Token::Exclam, Token::Ident("test".to_string()), Token::EOF], output)
    }

    #[test]
    fn exclam_equal() {
        let output = create_lexer("test != 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::ExclamEqual, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn less() {
        let output = create_lexer("test < 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::Less, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn greater() {
        let output = create_lexer("test > 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::Greater, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn less_equal() {
        let output = create_lexer("test <= 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::LessEqual, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn greater_equal() {
        let output = create_lexer("test >= 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::GreaterEqual, Token::Number(1f64), Token::EOF], output)
    }

    #[test]
    fn equal_equal() {
        let output = create_lexer("test == 1");
        assert_eq!(vec![Token::Ident("test".to_string()), Token::EqualEqual, Token::Number(1f64), Token::EOF], output)
    }
}