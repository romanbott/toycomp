use std::{fmt, str::FromStr};

use crate::automata::TaggedDFA;

#[derive(Debug, Clone)]
pub struct Pattern {
    pub regex: String,
    pub tag: String,
}

#[derive(Debug, Clone)]
pub struct Lexer {
    pub patterns: Vec<Pattern>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub tag: String,
    pub value: String,
    pub position: (usize, usize),
}

impl From<(&str, &str)> for Token {
    fn from((tag, value): (&str, &str)) -> Self {
        Token {
            tag: tag.to_string(),
            value: value.to_string(),
            position: (0, 0),
        }
    }
}

impl From<(&str, &str, usize, usize)> for Token {
    fn from((tag, value, row, col): (&str, &str, usize, usize)) -> Self {
        Token {
            tag: tag.to_string(),
            value: value.to_string(),
            position: (row, col),
        }
    }
}

#[derive(Debug)]
pub struct LexingError {
    pub position: usize,
    pub parsed_tokens: Vec<Token>,
    pub context: String,
}

impl fmt::Display for LexingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Lexing error at position {}. Context: \"{}\". Parsed tokens: {:?}",
            self.position, self.context, self.parsed_tokens
        )
    }
}

impl std::error::Error for LexingError {}

impl Lexer {
    pub fn consume(&self, input: &str) -> Result<Vec<Token>, LexingError> {
        let dfa: TaggedDFA = self.into();
        let min = dfa.minimize();

        let mut token_begin = 0;
        let mut scan = 0;

        let len = input.len();
        let mut tokens = Vec::new();
        let mut current_line = 0;
        let mut current_char = 0;

        while token_begin < len {
            let mut last_lenght = 0;
            let mut last_tag = "";
            while scan < len + 1 {
                if let Some(tag) = min.accept(&input[token_begin..scan]) {
                    last_tag = tag;
                    last_lenght = scan - token_begin;
                }
                scan += 1;
            }

            if last_lenght == 0 {
                let end = (token_begin + 10).min(len); // Take up to 10 chars as context
                let context = input[token_begin..end].to_string();

                return Err(LexingError {
                    position: token_begin,
                    parsed_tokens: tokens, // Return successfully parsed tokens up to this point
                    context: context,
                });
            }
            if &input.chars().nth(token_begin) == &Some('\n') {
                current_line += 1;
                current_char = 0
            }

            tokens.push(Token {
                tag: last_tag.to_owned(),
                value: input[token_begin..(token_begin + last_lenght)].to_owned(),
                position: (current_line, current_char),
            });

            current_char += last_lenght;
            token_begin += last_lenght;
            scan = token_begin;
        }

        Ok(tokens)
    }
}

#[derive(Debug)]
pub enum LexerParseError {
    InvalidFormat(String),
    EmptyInput,
}

impl fmt::Display for LexerParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LexerParseError::InvalidFormat(line) => write!(
                f,
                "Invalid pattern line format: \"{}\". Expected format: 'tag -> regex'",
                line
            ),
            LexerParseError::EmptyInput => write!(f, "Input string is empty."),
        }
    }
}

impl std::error::Error for LexerParseError {}

impl FromStr for Lexer {
    type Err = LexerParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.trim().is_empty() {
            return Err(LexerParseError::EmptyInput);
        }

        let mut patterns = Vec::new();

        for line in s.lines() {
            let trimmed_line = line.trim();

            // Skip lines that are empty or just whitespace
            if trimmed_line.is_empty() {
                continue;
            }

            // Split the line by the " -> " separator
            let parts = trimmed_line
                .split_once("->")
                .ok_or(LexerParseError::InvalidFormat(trimmed_line.to_string()))?;

            let tag = parts.0.trim().to_string();
            let regex = parts.1.trim().to_string();

            // Basic validation: ensure both parts aren't empty after trimming
            if tag.is_empty() || regex.is_empty() {
                return Err(LexerParseError::InvalidFormat(trimmed_line.to_string()));
            }

            patterns.push(Pattern { tag, regex });
        }

        Ok(Lexer { patterns })
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::{LexerParseError, Token};

    use super::{Lexer, Pattern};

    #[test]
    fn parsing_lexers() {
        let lex: Result<Lexer, LexerParseError> = r#"
            keyword ->(if)|(else)|(then)
            identifier ->(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z)+
            white_space ->\t|\r| |\n
        "#
        .parse();

        assert!(lex.is_ok());
    }

    #[test]
    fn lexing() {
        let lex: Lexer = r#"
            keyword ->(if)|(else)|(then)
            identifier ->(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z)+
            white_space ->\t|\r| |\n
        "#
        .parse()
        .unwrap();

        let tokens = lex.consume("if myvar then else");

        assert!(tokens.is_ok());

        let tokens = tokens.unwrap();

        let expected_tokens: Vec<Token> = vec![
            ("keyword", "if", 0, 0).into(),
            ("white_space", " ", 0, 2).into(),
            ("identifier", "myvar", 0, 3).into(),
            ("white_space", " ", 0, 8).into(),
            ("keyword", "then", 0, 9).into(),
            ("white_space", " ", 0, 13).into(),
            ("keyword", "else", 0, 14).into(),
        ];

        assert_eq!(expected_tokens, tokens);
    }
}
