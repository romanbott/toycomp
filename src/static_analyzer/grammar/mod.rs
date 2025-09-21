use std::collections::{BTreeMap, BTreeSet};

/// Represents a symbol in a formal grammar.
///
/// Symbols can be either a `Terminal`, a `NonTerminal`, or the special `End`
/// symbol which signifies the end of the input stream.
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum Symbol<'a> {
    /// A terminal symbol, e.g., 'a', 'b', '+'.
    Terminal(&'a str),
    /// A non-terminal symbol, e.g., 'S', 'A', 'B'.
    NonTerminal(&'a str),
    /// The end-of-input marker.
    End,
}

impl Symbol<'_> {
    /// Checks if the symbol is a non-terminal.
    ///
    /// # Returns
    ///
    /// `true` if the symbol is a `NonTerminal`, otherwise `false`.
    fn is_non_terminal(&self) -> bool {
        matches!(&self, Symbol::NonTerminal(_))
    }
}

/// Represents a production rule in a formal grammar.
///
/// A production rule consists of a `left` non-terminal symbol and a `right`
/// sequence of symbols.
#[derive(Debug, PartialEq)]
struct Production<'a> {
    /// The non-terminal symbol on the left side of the production.
    left: Symbol<'a>,
    /// The sequence of symbols on the right side of the production.
    right: Vec<Symbol<'a>>,
}

impl<'a> Production<'a> {
    /// Creates a production rule that generates an empty string (epsilon).
    ///
    /// # Arguments
    ///
    /// * `symbol` - The non-terminal symbol for the left side of the rule.
    ///
    /// # Returns
    ///
    /// A `Production` rule with the given symbol on the left and epsilon on the right.
    #[allow(dead_code)]
    fn empty(symbol: Symbol<'a>) -> Self {
        Production {
            left: symbol,
            right: vec![Symbol::Terminal("ε")],
        }
    }
}

/// Represents a formal grammar.
///
/// A grammar is defined by its set of non-terminals, terminals, production rules,
/// and a designated start symbol.
#[derive(Debug)]
struct Grammar<'a> {
    /// The set of all non-terminal symbols in the grammar.
    non_terminals: BTreeSet<Symbol<'a>>,
    /// The set of all terminal symbols in the grammar.
    terminals: BTreeSet<Symbol<'a>>,
    /// A list of all production rules.
    productions: Vec<Production<'a>>,
    /// The starting non-terminal symbol.
    start: Symbol<'a>,
}

/// An enumeration of possible errors that can occur during grammar parsing.
#[derive(Debug, PartialEq)]
pub enum ParseGrammarError {
    /// Indicates an invalid alternative format (e.g., epsilon mixed with other symbols).
    InvalidAlternative,
    /// Indicates an invalid line format (e.g., missing '->').
    InvalidFormat,
    /// Indicates that the input string was empty and contained no productions.
    NoProductions,
}

impl<'a> Grammar<'a> {
    /// Parses a string representation of a grammar into a `Grammar` struct.
    ///
    /// The string format should have one production per line, with the left-hand
    /// side separated from the right-hand side by `->`. Alternatives on the
    /// right-hand side are separated by `|`.
    ///
    /// # Arguments
    ///
    /// * `s` - A string slice containing the grammar definition.
    ///
    /// # Returns
    ///
    /// A `Result` containing the parsed `Grammar` on success, or a `ParseGrammarError`
    /// on failure.
    #[allow(dead_code)]
    pub fn from_str(s: &'a str) -> Result<Self, ParseGrammarError> {
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
            .ok_or(ParseGrammarError::InvalidFormat)?
            .trim();

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
                s.split_whitespace()
                    .next()
                    .ok_or(ParseGrammarError::InvalidFormat)
            })
            .collect();

        let non_terminal_chars: Vec<&str> = non_terminals?;

        let non_terminals_set: BTreeSet<&str> = non_terminal_chars.clone().into_iter().collect();

        let mut non_terminals = BTreeSet::new();

        for (nt, right_part) in non_terminal_chars.iter().zip(right) {
            let alternatives = right_part.trim().split("|");
            let left = Symbol::NonTerminal(nt);
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

    /// Computes the FIRST set for each symbol in the grammar.
    ///
    /// The FIRST set of a symbol is the set of terminal symbols that can appear
    /// as the first symbol in a string derived from that symbol.
    ///
    /// # Returns
    ///
    /// A `BTreeMap` where keys are `Symbol`s and values are `BTreeSet`s of
    /// `Symbol`s representing their FIRST sets.
    #[allow(dead_code)]
    pub fn get_first(&self) -> BTreeMap<Symbol<'_>, BTreeSet<Symbol<'_>>> {
        let mut curr_map = BTreeMap::new();

        // Initialize FIRST sets for terminals and non-terminals.
        for s in &self.terminals {
            curr_map.insert(*s, BTreeSet::from([*s]));
        }

        for s in &self.non_terminals {
            curr_map.insert(*s, BTreeSet::new());
        }

        // Loop while current map is different to next map
        loop {
            let mut next_map = curr_map.clone();

            // For every production of the form A -> X₁X₂...
            for prod in &self.productions {
                let first_left = next_map.get_mut(&prod.left).unwrap();

                let mut has_epsilon = true;

                //  For each symbol Xi in the right-hand side:
                for symbol in &prod.right {
                    let mut first_s = curr_map.get(symbol).unwrap().clone();
                    has_epsilon &= first_s.remove(&Symbol::Terminal("ε"));

                    //  Add FIRST(Xi) - {ε} to FIRST(A)
                    first_left.append(&mut first_s);

                    // If ε is'nt in FIRST(Xi), break
                    if !has_epsilon {
                        break;
                    }
                }

                // If ε is in FIRST(Xi) for all i, add ε to FIRST(A)
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

    /// Computes the FOLLOW set for each non-terminal in the grammar.
    ///
    /// The FOLLOW set of a non-terminal is the set of terminal symbols that
    /// can immediately follow that non-terminal in a valid string.
    ///
    /// # Returns
    ///
    /// A `BTreeMap` where keys are non-terminal `Symbol`s and values are
    /// `BTreeSet`s of `Symbol`s representing their FOLLOW sets.
    #[allow(dead_code)]
    pub fn get_follow(&self) -> BTreeMap<Symbol<'_>, BTreeSet<Symbol<'_>>> {
        let mut curr_map = BTreeMap::new();

        // Initialize FOLLOW sets. All start empty except for the initial symbol.
        for s in &self.non_terminals {
            if s == &self.start {
                curr_map.insert(*s, BTreeSet::from([Symbol::End]));
            } else {
                curr_map.insert(*s, BTreeSet::new());
            }
        }

        let first_sets = self.get_first();

        // Loop while current map is different to next map
        loop {
            let mut next_map = curr_map.clone();

            // For every production of the form A -> X₁X₂...
            for prod in &self.productions {
                let mut right = prod.right.clone();
                let mut remaining = right.as_mut_slice();

                while let Some((symbol, rest)) = remaining.split_first_mut() {
                    let mut has_epsilon = true;
                    // For each Xi (where Xi is a non-terminal):
                    if symbol.is_non_terminal() {
                        let follow_symbol = next_map.get_mut(symbol).unwrap();

                        // For each symbol Xj after Xi (i < j <= n):
                        for element in rest.iter() {
                            let mut first_of_element = first_sets.get(element).unwrap().clone();
                            has_epsilon &= first_of_element.remove(&Symbol::Terminal("ε"));
                            // Add FIRST(Xj) - {ε} to FOLLOW(Xi)
                            follow_symbol.append(&mut first_of_element);
                            // If ε is'nt in FIRST(Xj), break
                            if !has_epsilon {
                                break;
                            }
                        }

                        // If ε is in FIRST(Xj) for all j > i, add FOLLOW(B) to FOLLOW(Xi)
                        if has_epsilon {
                            follow_symbol.append(&mut curr_map.get(&prod.left).unwrap().clone());
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

    use crate::static_analyzer::grammar::{Grammar, Symbol};

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
        #[allow(non_snake_case)]
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
        #[allow(non_snake_case)]
        let follow_S = follow_sets.get(&Symbol::NonTerminal("S")).unwrap();

        assert!(follow_S.contains(&Symbol::End))
    }

    #[test]
    fn epsilon_production_first() {
        let grammar = "S -> ε|a";

        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let first_sets = parsed_grammar.get_first();
        #[allow(non_snake_case)]
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
        #[allow(non_snake_case)]
        let follow_A = follow_sets.get(&Symbol::NonTerminal("A")).unwrap();
        #[allow(non_snake_case)]
        let follow_B = follow_sets.get(&Symbol::NonTerminal("B")).unwrap();

        assert!(follow_A.contains(&Symbol::Terminal("b")));
        assert!(follow_B.contains(&Symbol::End));
    }

    #[test]
    fn complex_grammar() {
        let grammar = "program     -> stmt_list
            stmt_list   -> stmt stmt_list | ε
            stmt        -> decl_stmt | assign_stmt | if_stmt | while_stmt | print_stmt
            decl_stmt   -> type ID ;
            type        -> int | float | bool
            assign_stmt -> ID = expr ;
            if_stmt     -> if ( bool_expr ) { stmt_list } else { stmt_list }
            while_stmt  -> while ( bool_expr ) { stmt_list }
            print_stmt  -> print expr ;
            bool_expr   -> expr relop expr
            relop       -> < | <= | > | >= | == | !=
            expr        -> term expr_prime
            expr_prime  -> + term expr_prime | - term expr_prime | ε
            term        -> factor term_prime
            term_prime  -> * factor term_prime | / factor term_prime | ε
            factor      -> ( expr ) | ID | NUM";

        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let follow_sets = parsed_grammar.get_follow();

        let follow_relop = follow_sets.get(&Symbol::NonTerminal("relop")).unwrap();
        assert!(follow_relop.contains(&Symbol::Terminal("ID")));
        assert!(follow_relop.contains(&Symbol::Terminal("NUM")));
        assert!(follow_relop.contains(&Symbol::Terminal("(")));
    }
}
