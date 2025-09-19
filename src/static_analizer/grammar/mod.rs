use std::{collections::BTreeSet, str::FromStr};

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum Symbol {
    Terminal(char),
    NonTerminal(char),
}

#[derive(Debug, PartialEq)]
struct Production {
    left: Symbol,
    right: Vec<Symbol>,
}

impl Production {
    fn empty(symbol: Symbol) -> Self {
        Production {
            left: symbol,
            right: vec![],
        }
    }
}

#[derive(Debug)]
struct Grammar {
    non_terminals: BTreeSet<Symbol>,
    terminals: BTreeSet<Symbol>,
    productions: Vec<Production>,
    start: Symbol,
}

#[derive(Debug, PartialEq)]
pub enum ParseGrammarError {
    InvalidAlternative,
    InvalidFormat,
    UndefinedSymbol(char),
    NoProductions,
}

impl FromStr for Grammar {
    type Err = ParseGrammarError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut productions: Vec<Production> = Vec::new();
        let mut terminals: BTreeSet<Symbol> = BTreeSet::new();

        let mut lines = s.lines().peekable();

        if lines.peek().is_none() {
            return Err(ParseGrammarError::NoProductions);
        }

        let start_char = lines
            .peek()
            .unwrap()
            .trim()
            .chars()
            .next()
            .ok_or(ParseGrammarError::InvalidFormat)?;

        let res: Result<Vec<_>, _> = lines
            .map(|line| {
                let split: Vec<&str> = line.split("->").collect();
                if split.len() == 2 {
                    Ok((split[0], split[1]))
                } else {
                    Err(ParseGrammarError::InvalidFormat)
                }
            })
            .collect();

        let (left, right): (Vec<_>, Vec<_>) = res?.into_iter().unzip();

        let non_terminals: Result<Vec<_>, _> = left
            .iter()
            .map(|s| {
                s.trim()
                    .chars()
                    .next()
                    .ok_or(ParseGrammarError::InvalidFormat)
            })
            .collect();

        let non_terminal_chars: Vec<char> = non_terminals?;

        let non_terminals_set: BTreeSet<char> = non_terminal_chars.clone().into_iter().collect();

        let mut non_terminals = BTreeSet::new();

        for (nt, right_part) in non_terminal_chars.iter().zip(right) {
            let alternatives = right_part.trim().split("|");
            let left = Symbol::NonTerminal(*nt);
            non_terminals.insert(left);

            for alternative in alternatives {
                match (alternative.trim().contains('ε'), alternative) {
                    (true, "ε") => productions.push(Production::empty(left)),
                    (true, _) => return Err(ParseGrammarError::InvalidAlternative),
                    (false, _) => {
                        let prod_right = alternative
                            .chars()
                            .map(|c| {
                                if non_terminals_set.contains(&c) {
                                    Symbol::NonTerminal(c)
                                } else {
                                    let terminal = Symbol::Terminal(c);
                                    terminals.insert(terminal);
                                    terminal
                                }
                            })
                            .collect();

                        productions.push(Production {
                            left,
                            right: prod_right,
                        });
                    }
                }
            }
        }

        Ok(Grammar {
            non_terminals,
            terminals,
            productions,
            start: Symbol::NonTerminal(start_char),
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::static_analizer::grammar::{Grammar, Symbol};

    #[test]
    fn parse_grammar() {
        let grammar = r#"S -> s|ε
        T -> a|b"#;

        let parsed_grammar: Result<Grammar, _> = grammar.parse();

        assert!(parsed_grammar.is_ok());
        let parsed_grammar = parsed_grammar.unwrap();

        assert_eq!(
            parsed_grammar.terminals,
            BTreeSet::from([
                Symbol::Terminal('s'),
                Symbol::Terminal('a'),
                Symbol::Terminal('b')
            ])
        )
    }
}
