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

#[cfg(test)]
mod tests {
    use crate::lexer::Token;

    use super::{Lexer, Pattern};

    #[test]
    fn lexing() {
        let lex = Lexer {
            patterns: vec![
                Pattern {
                    regex: "(if)|(else)|(then)".to_string(),
                    tag: "keyword".to_string(),
                },
                Pattern {
                    regex: "(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z)+".to_string(),
                    tag: "identifier".to_string(),
                },
                Pattern {
                    regex: " |\t|\r|\n".to_string(),
                    tag: "white space".to_string(),
                },
            ],
        };

        let tokens = lex.consume("if myvar then else");

        let expected_tokens = vec![
            Token {
                tag: "keyword".to_owned(),
                value: "if".to_owned(),
            },
            Token {
                tag: "white space".to_owned(),
                value: " ".to_owned(),
            },
            Token {
                tag: "identifier".to_owned(),
                value: "myvar".to_owned(),
            },
            Token {
                tag: "white space".to_owned(),
                value: " ".to_owned(),
            },
            Token {
                tag: "keyword".to_owned(),
                value: "then".to_owned(),
            },
            Token {
                tag: "white space".to_owned(),
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
