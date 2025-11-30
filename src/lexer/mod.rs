use std::{fmt, str::FromStr};

use crate::automata::TaggedDFA;

pub struct Pattern {
    pub regex: String,
    pub tag: String,
}

pub struct Lexer {
    pub patterns: Vec<Pattern>,
}

#[derive(Debug, PartialEq)]
pub struct Token {
    pub tag: String,
    pub value: String,
}

impl Lexer {
    pub fn consume(&self, input: &str) -> Vec<Token> {
        let dfa: TaggedDFA = self.into();
        let min = dfa.minimize();

        let mut token_begin = 0;
        let mut scan = 0;

        let len = input.len();
        let mut tokens = Vec::new();

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
                panic!(
                    "Lexing error at position {}\n.Parsed tokens: {:?}",
                    token_begin, tokens
                );
            }

            tokens.push(Token {
                tag: last_tag.to_owned(),
                value: input[token_begin..(token_begin + last_lenght)].to_owned(),
            });

            token_begin += last_lenght;
            scan = token_begin;
        }

        tokens
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
            let parts: Vec<&str> = trimmed_line.split("->").collect();

            if parts.len() != 2 {
                // Return an error if the line doesn't split correctly
                return Err(LexerParseError::InvalidFormat(trimmed_line.to_string()));
            }

            let tag = parts[0].trim().to_string();
            let regex = parts[1].trim().to_string();

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

        let expected_tokens = vec![
            Token {
                tag: "keyword".to_owned(),
                value: "if".to_owned(),
            },
            Token {
                tag: "white_space".to_owned(),
                value: " ".to_owned(),
            },
            Token {
                tag: "identifier".to_owned(),
                value: "myvar".to_owned(),
            },
            Token {
                tag: "white_space".to_owned(),
                value: " ".to_owned(),
            },
            Token {
                tag: "keyword".to_owned(),
                value: "then".to_owned(),
            },
            Token {
                tag: "white_space".to_owned(),
                value: " ".to_owned(),
            },
            Token {
                tag: "keyword".to_owned(),
                value: "else".to_owned(),
            },
        ];

        dbg!(&tokens);

        assert_eq!(expected_tokens, tokens);
    }
}
