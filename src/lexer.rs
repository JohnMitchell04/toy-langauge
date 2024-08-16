use std::{error::Error, fmt::Display, iter::Peekable, ops::DerefMut, str::Chars};

use crate::trace;

#[derive(Debug, Clone, PartialEq)]
// TODO: At some point change tokens to hold references to the source code, this will require an extensive lifetimes rework however
pub enum Token {
    // Single character tokens
    Comma, Semicolon, LParen, RParen, LBrace, RBrace,

    // Keywords
    Fun, Extern, For, If, Else, Unary, Binary, Var,

    // User data
    Comment, Ident(String), Number(f64), Op(char),

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
            Self::Comma => write!(f, ","),
            Self::Semicolon => write!(f, ";"),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::Fun => write!(f, "fun"),
            Self::Extern => write!(f, "extern"),
            Self::For => write!(f, "for"),
            Self::If => write!(f, "if"),
            Self::Else => write!(f, "else"),
            Self::Unary => write!(f, "unary"),
            Self::Binary => write!(f, "binary"),
            Self::Var => write!(f, "var"),
            Self::Comment => write!(f, "Comment"),
            Self::Ident(ident) => write!(f, "Identifier: {}", ident),
            Self::Number(num) => write!(f, "Number: {}", &num.to_string()),
            Self::Op(op) => write!(f, "Operator: {}", &op.to_string()),
            Self::EOF => write!(f, "EOF"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct LexError {
    pub message: &'static str,
    pub section: String,
    pub col: usize,
    pub line: usize,
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
    input: &'a str,
    chars: Box<Peekable<Chars<'a>>>,
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer on the given input.
    pub fn new(input: &'a str) -> Self {
        Lexer { input, chars: Box::new(input.chars().peekable()), pos: 0, line: 1, col: 1 }
    }

    /// Retrieve the next token
    pub fn next_token(&mut self) -> LexResult {
        self.skip_whitespace();

        let chars = self.chars.deref_mut();
        let character = chars.next();
        self.pos += 1;
        self.col += 1;

        let result = match character {
            Some(',') => Ok(Token::Comma),
            Some(';') => Ok(Token::Semicolon),
            Some('(') => Ok(Token::LParen),
            Some(')') => Ok(Token::RParen),
            Some('{') => Ok(Token::LBrace),
            Some('}') => Ok(Token::RBrace),
            Some('/') => Ok(self.potential_comment()),
            Some('0'..='9') => self.parse_number(),
            Some('a'..='z' | 'A'..='Z' | '_') => self.parse_ident(),
            Some('+' | '-' | '<' | '>' | '*' | '=' | '!') => Ok(Token::Op(character.unwrap())),
            Some(_) => Err(LexError::new("Unexpected character", self.input[self.pos - 1..self.pos].to_string(), self.col - 1, self.line)),
            None => Ok(Token::EOF),
        };

        if cfg!(debug_assertions) {
            self.trace_result(&result);
        }
        
        result
    }

    /// Parse an identifier or keyword
    fn parse_ident(&mut self) -> LexResult {
        let start = self.pos - 1;
        let col_start = self.col - 1;

        loop {
            let char = match self.chars.peek() {
                Some(char) => *char,
                None => break,
            };

            if char != '_' && !char.is_alphanumeric() { break; }

            self.chars.next();
            self.pos += 1;
            self.col += 1;
        }

        if let Some(&char) = self.chars.peek() {
            if !char.is_whitespace() && !matches!(char, '+' | '-' | '<' | '>' | '*' | '/' | '(' | ')' | ',' | ';') {
                while let Some(char) = self.chars.peek() {
                    if char.is_whitespace() { break }

                    self.chars.next();
                    self.pos += 1;
                    self.col += 1;
                }

                return Err(LexError::new("Invalid identifier", self.input[start..self.pos].to_string(), col_start, self.line))
            }
        }

        // Keywords
        match &self.input[start..self.pos] {
            "fun" => Ok(Token::Fun),
            "extern" => Ok(Token::Extern),
            "if" => Ok(Token::If),
            "else" => Ok(Token::Else),
            "for" => Ok(Token::For),
            "unary" => Ok(Token::Unary),
            "binary" => Ok(Token::Binary),
            "var" => Ok(Token::Var),
            ident => Ok(Token::Ident(ident.to_string())),
        }
    }

    /// Parse a number literal
    fn parse_number(&mut self) -> LexResult {
        let start = self.pos - 1;
        let col_start = self.col - 1;

        loop {
            let ch = match self.chars.peek() {
                Some(ch) => *ch,
                None => break,
            };

            if ch != '.' && !ch.is_ascii_hexdigit() { break; }

            self.chars.next();
            self.pos += 1;
            self.col += 1;
        }

        if let Some(&char) = self.chars.peek() {
            if !char.is_whitespace() && !matches!(char, '+' | '-' | '<' | '>' | '*' | '/' | '(' | ')' | ',' | ';') {
                while let Some(char) = self.chars.peek() {
                    if char.is_whitespace() { break }

                    self.chars.next();
                    self.pos += 1;
                    self.col += 1;
                }

                return Err(LexError::new("Invalid identifier", self.input[start..self.pos].to_string(), col_start, self.line))
            }
        }

        match self.input[start..self.pos].parse() {
            Ok(num) => Ok(Token::Number(num)),
            Err(_) => Err(LexError::new("Invalid number format", self.input[start..self.pos].to_string(), col_start, self.line)),
        }
    }

    /// Parse a potential comment.
    fn potential_comment(&mut self) -> Token {
        if let Some('/') = self.chars.peek() {
            loop {
                let char = self.chars.next();
                self.pos += 1;

                if char == Some('\n') || char == None { break; }
            }

            self.col = 1;
            self.line += 1;

            Token::Comment
        } else {
            Token::Op('/')
        }
    }

    /// Skip whitespace characters.
    fn skip_whitespace(&mut self) {
        while let Some(&char) = self.chars.peek() {
            if !char.is_whitespace() { break }
    
            self.chars.next();
            self.pos += 1;
            if char == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
    }

    #[cfg(debug_assertions)]
    fn trace_result(&self, result: &LexResult) {
        match result {
            Ok(token) => trace!("{}", token),
            Err(err) => trace!("{}", err)
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = LexResult<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.next_token())
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::LexError;
    use super::{LexResult, Lexer, Token};

    fn create_lexer(input: &str) -> Vec<Token> {
        let lexer = Lexer::new(input);
        let mut temp: Vec<Token> = lexer.into_iter().take_while(|res| *res.as_ref().unwrap() != Token::EOF).map(|res| res.unwrap()).collect();
        temp.push(Token::EOF);
        temp
    }

    fn create_lexer_res(input: &str) -> LexResult {
        let mut lexer = Lexer::new(input);
        lexer.next_token()
    }

    #[test]
    fn comment() {
        let output = create_lexer("// this is a comment");
        assert_eq!(vec![Token::Comment, Token::EOF], output)
    }

    #[test]
    fn integer() {
        let output = create_lexer("5");
        assert_eq!(vec![Token::Number(5f64), Token::EOF], output)
    }

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
    fn invalid_number() {
        let output = create_lexer_res("5test");
        assert_eq!(Err(LexError::new("Invalid identifier", "5test".to_string(), 1, 1)), output)
    }

    #[test]
    fn numeric_simple() {
        let output = create_lexer("5 + 5");
        assert_eq!(vec![Token::Number(5f64), Token::Op('+'), Token::Number(5f64), Token::EOF], output)
    }

    #[test]
    fn numeric_complex() {
        let output = create_lexer("(5+5) * 5");
        assert_eq!(vec![Token::LParen, Token::Number(5f64), Token::Op('+'), Token::Number(5f64), Token::RParen, Token::Op('*'), Token::Number(5f64), Token::EOF], output)
    }

    #[test]
    fn assign_expr() {
        let output = create_lexer("var test = 5;");
        assert_eq!(vec![Token::Var, Token::Ident("test".to_string()), Token::Op('='), Token::Number(5f64), Token::Semicolon, Token::EOF], output)
    }

    #[test]
    fn for_loop() {
        let output = create_lexer("for (x = 5; x < 10; x = x + 1) { var test = 5; }");
        assert_eq!(
            vec![
                Token::For, Token::LParen, Token::Ident("x".to_string()), Token::Op('='), Token::Number(5f64), Token::Semicolon, Token::Ident("x".to_string()),
                Token::Op('<'), Token::Number(10f64), Token::Semicolon, Token::Ident("x".to_string()), Token::Op('='), Token::Ident("x".to_string()),
                Token::Op('+'), Token::Number(1f64), Token::RParen, Token::LBrace, Token::Var, Token::Ident("test".to_string()), Token::Op('='), Token::Number(5f64),
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
}