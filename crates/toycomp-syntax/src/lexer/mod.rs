use std::{collections::BTreeMap, fmt, str::FromStr};

use crate::{
    automata::{Arrow, NDFA, NDTable, TaggedDFA, TaggedNDFA},
    grammar::Symbol,
};

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
        Self::scan(&dfa.minimize(), input)
    }

    /// Scans `input` with an already compiled DFA.
    ///
    /// This is a single pass: each token walks the DFA only as far as that
    /// token can possibly go, instead of re-running it over every prefix of the
    /// remaining input.
    pub fn scan<D: Dfa>(dfa: &D, input: &str) -> Result<Vec<Token>, LexingError> {
        let len = input.len();
        let mut tokens = Vec::new();
        let mut token_begin = 0;
        let mut line = 0;
        let mut column = 0;

        while token_begin < len {
            let rest = &input[token_begin..];
            let mut state = dfa.initial();
            let mut best: Option<(usize, &str)> = None;

            for (offset, c) in rest.char_indices() {
                match dfa.step(state, c) {
                    Some(next) => {
                        state = next;
                        if let Some(tag) = dfa.tag(state) {
                            best = Some((offset + c.len_utf8(), tag));
                        }
                    }
                    None => break,
                }
            }

            let Some((length, tag)) = best else {
                let context = rest.chars().take(10).collect::<String>();
                return Err(LexingError {
                    position: token_begin,
                    parsed_tokens: tokens,
                    context,
                });
            };

            let end = token_begin + length;
            let value = &input[token_begin..end];

            tokens.push(Token {
                tag: tag.to_owned(),
                value: value.to_owned(),
                position: (line, column),
            });

            for c in value.chars() {
                if c == '\n' {
                    line += 1;
                    column = 0;
                } else {
                    column += 1;
                }
            }

            token_begin = end;
        }

        Ok(tokens)
    }
}

/// A deterministic automaton that can drive `Lexer::scan`.
pub trait Dfa {
    fn initial(&self) -> usize;
    fn step(&self, state: usize, c: char) -> Option<usize>;
    fn tag(&self, state: usize) -> Option<&str>;
}

impl Dfa for TaggedDFA {
    fn initial(&self) -> usize {
        TaggedDFA::initial_state(self)
    }

    fn step(&self, state: usize, c: char) -> Option<usize> {
        self.move_c(state, c)
    }

    fn tag(&self, state: usize) -> Option<&str> {
        TaggedDFA::tag(self, state)
    }
}

/// A DFA in `&'static` form, emitted by `build.rs`/`lexgen`.
pub struct StaticDFA {
    pub initial_state: u16,
    pub transitions: &'static [&'static [(char, u16)]],
    /// One entry per state: tag id, or `u16::MAX` if not final.
    pub final_tag: &'static [u16],
    pub tag_names: &'static [&'static str],
}

impl Dfa for StaticDFA {
    fn initial(&self) -> usize {
        self.initial_state as usize
    }

    fn step(&self, state: usize, c: char) -> Option<usize> {
        self.transitions
            .get(state)?
            .iter()
            .find_map(|(label, target)| (*label == c).then_some(*target as usize))
    }

    fn tag(&self, state: usize) -> Option<&str> {
        let tag = *self.final_tag.get(state)?;
        if tag == u16::MAX {
            None
        } else {
            self.tag_names.get(tag as usize).copied()
        }
    }
}

/// Owned DFA data, used by the generators.
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize, bincode::Encode, bincode::Decode)
)]
pub struct DfaData {
    pub initial_state: u16,
    pub transitions: Vec<Vec<(char, u16)>>,
    pub final_tag: Vec<u16>,
    pub tag_names: Vec<String>,
}

impl DfaData {
    pub fn from_tagged(dfa: &TaggedDFA) -> Self {
        let transitions = dfa
            .transitions()
            .iter()
            .map(|row| row.iter().map(|a| (a.label(), a.target() as u16)).collect())
            .collect();

        let mut tag_names: Vec<String> = Vec::new();
        let mut final_tag = vec![u16::MAX; dfa.num_states()];
        for (state, tag) in dfa.final_state_tags() {
            let id = match tag_names.iter().position(|t| t == tag) {
                Some(id) => id,
                None => {
                    tag_names.push(tag.clone());
                    tag_names.len() - 1
                }
            };
            final_tag[*state] = id as u16;
        }

        DfaData {
            initial_state: dfa.initial_state() as u16,
            transitions,
            final_tag,
            tag_names,
        }
    }

    pub fn to_rust_source(&self) -> String {
        let mut out = String::new();
        out.push_str("use toycomp_syntax::StaticDFA;\n\n");
        out.push_str("pub static DFA: StaticDFA = StaticDFA {\n");
        use std::fmt::Write as _;
        writeln!(out, "    initial_state: {},", self.initial_state).unwrap();
        out.push_str("    transitions: &[\n");
        for row in &self.transitions {
            out.push_str("        &[");
            for (i, (label, target)) in row.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write!(out, "({label:?}, {target})").unwrap();
            }
            out.push_str("],\n");
        }
        out.push_str("    ],\n");
        writeln!(out, "    final_tag: &{:?},", self.final_tag).unwrap();
        out.push_str("    tag_names: &[");
        for (i, tag) in self.tag_names.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            write!(out, "{tag:?}").unwrap();
        }
        out.push_str("],\n");
        out.push_str("};\n");
        out
    }
}

impl From<&Lexer> for TaggedNDFA {
    fn from(lexer: &Lexer) -> Self {
        let tagged_ndfas: Vec<(String, NDFA)> = lexer
            .patterns
            .iter()
            .map(|p| (p.tag.clone(), NDFA::from_regex(p.regex.as_str())))
            .collect();

        let mut shifted_tables: Vec<Vec<Vec<Arrow>>> = Vec::new();
        let mut total_shift = 0;
        let mut starting_states: Vec<usize> = Vec::new();
        let mut final_states: BTreeMap<usize, String> = BTreeMap::new();

        for (tag, ndfa) in tagged_ndfas {
            starting_states.push(ndfa.initial_state + total_shift);
            final_states.insert(ndfa.final_state + total_shift, tag);

            shifted_tables.push(
                ndfa.table
                    .0
                    .iter()
                    .map(|row| {
                        row.iter()
                            .map(|arrow| arrow.move_target(total_shift))
                            .collect()
                    })
                    .collect(),
            );

            total_shift += ndfa.table.0.len();
        }

        let mut table = shifted_tables.concat();

        // Add epsilon transitions from a new initial state to every pattern's
        // initial state.
        table.push(starting_states.iter().map(|s| Arrow::Epsilon(*s)).collect());

        let initial_state = table.len() - 1;

        TaggedNDFA {
            table: NDTable(table),
            initial_state,
            final_states,
        }
    }
}

impl From<&Lexer> for TaggedDFA {
    fn from(lexer: &Lexer) -> Self {
        let ndfa: TaggedNDFA = lexer.into();
        ndfa.into()
    }
}

impl<'a> From<&'a Token> for Symbol<'a> {
    fn from(value: &'a Token) -> Self {
        if value.tag == "<END>" {
            return Symbol::End;
        }
        Symbol::Terminal(value.tag.as_str())
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
    fn positions_after_newline() {
        let lex: Lexer = "ID->a|b\nWS->\\n".parse().unwrap();

        let tokens = lex.consume("a\nb").unwrap();

        let expected: Vec<Token> = vec![
            ("ID", "a", 0, 0).into(),
            ("WS", "\n", 0, 1).into(),
            ("ID", "b", 1, 0).into(),
        ];
        assert_eq!(expected, tokens);
    }

    #[test]
    fn non_ascii_is_an_error() {
        let lex: Lexer = "ID->a|b\nOTHER->é".parse().unwrap();

        // Must not panic on a UTF-8 boundary; it is simply an unmatched char.
        assert!(lex.consume("aé").is_ok());
        assert!(lex.consume("a@").is_err());
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
