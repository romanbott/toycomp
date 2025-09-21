use std::{
    collections::{BTreeMap, BTreeSet},
};

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum Symbol<'a> {
    Terminal(&'a str),
    NonTerminal(&'a str),
    End,
}

impl Symbol<'_> {
    fn is_non_terminal(&self) -> bool {
        matches!(&self, Symbol::NonTerminal(_))
    }
}

#[derive(Debug, PartialEq)]
struct Production<'a> {
    left: Symbol<'a>,
    right: Vec<Symbol<'a>>,
}

impl<'a> Production<'a> {
    fn empty(symbol: Symbol<'a>) -> Self {
        Production {
            left: symbol,
            right: vec![Symbol::Terminal("ε")],
        }
    }
}

#[derive(Debug)]
struct Grammar<'a> {
    non_terminals: BTreeSet<Symbol<'a>>,
    terminals: BTreeSet<Symbol<'a>>,
    productions: Vec<Production<'a>>,
    start: Symbol<'a>,
}

#[derive(Debug, PartialEq)]
pub enum ParseGrammarError {
    InvalidAlternative,
    InvalidFormat,
    UndefinedSymbol(char),
    NoProductions,
}

impl<'a> Grammar<'a> {
    fn from_str(s: &'a str) -> Result<Self, ParseGrammarError> {
        let mut productions: Vec<Production> = Vec::new();
        let mut terminals: BTreeSet<Symbol> = BTreeSet::new();

        let mut lines = s.lines().peekable();

        if lines.peek().is_none() {
            return Err(ParseGrammarError::NoProductions);
        }

        let start_char = lines
            .peek()
            .unwrap()
            .split("->")
            .next()
            .ok_or(ParseGrammarError::InvalidFormat)?.trim();

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
                    .split_whitespace()
                    .next()
                    .ok_or(ParseGrammarError::InvalidFormat)
            })
            .collect();

        let non_terminal_chars: Vec<&str> = non_terminals?;

        let non_terminals_set: BTreeSet<&str> = non_terminal_chars.clone().into_iter().collect();

        let mut non_terminals = BTreeSet::new();

        for (nt, right_part) in non_terminal_chars.iter().zip(right) {
            let alternatives = right_part.trim().split("|");
            let left = Symbol::NonTerminal(*nt);
            non_terminals.insert(left);

            for alternative in alternatives {
                if alternative.trim().contains('ε') & (alternative.trim() != "ε") {
                    return Err(ParseGrammarError::InvalidAlternative);
                }

                let prod_right = alternative
                    .split_whitespace()
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

        Ok(Grammar {
            non_terminals,
            terminals,
            productions,
            start: Symbol::NonTerminal(start_char),
        })
    }

    fn get_first(&self) -> BTreeMap<Symbol, BTreeSet<Symbol>> {
        let mut curr_map = BTreeMap::new();

        for s in &self.terminals {
            curr_map.insert(s.clone(), BTreeSet::from([*s]));
        }

        for s in &self.non_terminals {
            curr_map.insert(s.clone(), BTreeSet::new());
        }

        loop {
            let mut next_map = curr_map.clone();

            for prod in &self.productions {
                let first_left = next_map.get_mut(&prod.left).unwrap();

                let mut has_epsilon = true;
                for s in &prod.right {
                    let mut first_s = curr_map.get(s).unwrap().clone();
                    has_epsilon &= first_s.remove(&Symbol::Terminal("ε"));
                    first_left.append(&mut first_s);
                    if !has_epsilon {
                        break;
                    }
                }
                if has_epsilon {
                    first_left.insert(Symbol::Terminal("ε"));
                }
            }

            if curr_map == next_map {
                return curr_map;
            }
            curr_map = next_map
        }
    }

    fn get_follow(&self) -> BTreeMap<Symbol, BTreeSet<Symbol>> {
        let mut curr_map = BTreeMap::new();

        for s in &self.non_terminals {
            if s == &self.start {
                curr_map.insert(s.clone(), BTreeSet::from([Symbol::End]));
            } else {
                curr_map.insert(s.clone(), BTreeSet::new());
            }
        }

        let first_sets = self.get_first();

        loop {
            let mut next_map = curr_map.clone();

            for prod in &self.productions {
                let mut right = prod.right.clone();
                let mut remaining = right.as_mut_slice();

                while let Some((first_symbol, rest)) = remaining.split_first_mut() {
                    let mut has_epsilon = true;
                    if first_symbol.is_non_terminal() {
                        let follow_first_symbol = next_map.get_mut(first_symbol).unwrap();

                        for element in rest.iter() {
                            let mut first_of_element = first_sets.get(element).unwrap().clone();
                            has_epsilon &= first_of_element.remove(&Symbol::Terminal("ε"));
                            follow_first_symbol.append(&mut first_of_element);
                            if !has_epsilon {
                                break;
                            }
                        }

                        if has_epsilon {
                            follow_first_symbol
                                .append(&mut curr_map.get(&prod.left).unwrap().clone());
                        }
                    }
                    remaining = rest;
                }
            }

            if curr_map == next_map {
                return curr_map;
            }
            curr_map = next_map
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::static_analizer::grammar::{Grammar, Symbol};

    #[test]
    fn parse_grammar() {
        let grammar = r#"S -> s|ε
        T -> a c|b"#;

        let parsed_grammar = Grammar::from_str(grammar);

        assert!(parsed_grammar.is_ok());
        let parsed_grammar = parsed_grammar.unwrap();

        assert_eq!(
            parsed_grammar.terminals,
            BTreeSet::from([
                Symbol::Terminal("s"),
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::Terminal("c"),
                Symbol::Terminal("ε"),
            ])
        )
    }

    #[test]
    fn simple_grammar_first() {
        let grammar = "S -> a S|b";

        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let first_sets = parsed_grammar.get_first();
        let first_S = first_sets.get(&Symbol::NonTerminal("S")).unwrap();

        assert_eq!(
            first_S,
            &BTreeSet::from([Symbol::Terminal("a"), Symbol::Terminal("b"),])
        )
    }

    #[test]
    fn simple_grammar_follow() {
        let grammar = "S -> a S|b";

        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let follow_sets = parsed_grammar.get_follow();
        let follow_S = follow_sets.get(&Symbol::NonTerminal("S")).unwrap();

        assert!(follow_S.contains(&Symbol::End))
    }

    #[test]
    fn epsilon_production_first() {
        let grammar = "S -> ε|a";

        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let first_sets = parsed_grammar.get_first();
        let first_S = first_sets.get(&Symbol::NonTerminal("S")).unwrap();

        assert_eq!(
            first_S,
            &BTreeSet::from([Symbol::Terminal("a"), Symbol::Terminal("ε"),])
        )
    }

    #[test]
    fn multiple_non_terminals_follow() {
        let grammar = "S -> A B
A -> a
B -> b";

        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let follow_sets = parsed_grammar.get_follow();
        let follow_A = follow_sets.get(&Symbol::NonTerminal("A")).unwrap();
        let follow_B = follow_sets.get(&Symbol::NonTerminal("B")).unwrap();

        dbg!(&parsed_grammar);
        dbg!(follow_A);
        dbg!(follow_B);

        assert!(follow_A.contains(&Symbol::Terminal("b")));
        assert!(follow_B.contains(&Symbol::End));
    }

    #[test]
    fn complex_grammar() {
        let grammar = "program -> stmt_list
stmt_list -> stmt stmt_list | ε
stmt -> decl_stmt | assign_stmt | if_stmt | while_stmt | print_stmt
decl_stmt -> type ID ;
type -> int | float | bool
assign_stmt -> ID = expr ;
if_stmt -> if ( bool_expr ) { stmt_list } else { stmt_list }
while_stmt -> while ( bool_expr ) { stmt_list }
print_stmt -> print expr ;
bool_expr -> expr relop expr
relop -> < | <= | > | >= | == | !=
expr -> term expr_prime
expr_prime -> + term expr_prime | - term expr_prime | ε
term -> factor term_prime
term_prime -> * factor term_prime | / factor term_prime | ε
factor -> ( expr ) | ID | NUM";

        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let first_sets = parsed_grammar.get_first();
        let follow_sets = parsed_grammar.get_follow();

        let follow_relop = follow_sets.get(&Symbol::NonTerminal("relop")).unwrap();
        assert!(follow_relop.contains(&Symbol::Terminal("ID")));
        assert!(follow_relop.contains(&Symbol::Terminal("NUM")));
        assert!(follow_relop.contains(&Symbol::Terminal("(")));
    }
}
