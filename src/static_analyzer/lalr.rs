use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::{Display, Formatter},
    vec,
};

use crate::static_analyzer::{
    grammar::{self, Grammar, Production, Symbol},
    lr_parser::{LR1AutomatonState, LR1Item},
};

#[derive(PartialEq, Eq, Hash, Ord, PartialOrd, Clone, Debug)]
struct LALR1Item<'a> {
    prod: Production<'a>,
    dot: usize,
}

#[derive(PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct Core<'a>(BTreeSet<LALR1Item<'a>>);

impl<'a, 'b> From<&'b LR1AutomatonState<'a>> for Core<'a> {
    fn from(state: &'b LR1AutomatonState<'a>) -> Self {
        Core(state.0.iter().map(|item| item.into()).collect())
    }
}

impl<'a, 'b> From<&'b LR1Item<'a>> for LALR1Item<'a> {
    fn from(item: &'b LR1Item<'a>) -> Self {
        LALR1Item {
            prod: item.prod.clone(),
            dot: item.dot,
        }
    }
}

#[derive(Debug)]
enum ParseError<'a> {
    CantReduce(Production<'a>),
    NotExpected((Symbol<'a>, Vec<Symbol<'a>>)),
    EndWhileParsing,
}

impl<'a> Display for ParseError<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::CantReduce(prod) => {
                write!(
                    f,
                    "Parsing failed: Cannot reduce using production: {:?}",
                    prod
                )
            }
            ParseError::NotExpected((found_symbol, expected_symbols)) => {
                // Format the Vec<Symbol<'a>> into a single string for display
                let expected_str = expected_symbols
                    .iter()
                    .map(|sym| sym.to_string()) // Convert each Symbol to a String
                    .collect::<Vec<String>>() // Collect into a Vec<String>
                    .join(", "); // Join with commas and spaces

                write!(
                    f,
                    "Found: {} while expecting: {}",
                    found_symbol, expected_str
                )
            }
            ParseError::EndWhileParsing => {
                write!(f, "Unexpected end of input while parsing.")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum LALRAction<'a> {
    Shift(usize),
    Reduce(Production<'a>),
    Accept,
    Goto(usize),
}

#[derive(Debug)]
struct LALRAutomaton<'a> {
    table: HashMap<(usize, Symbol<'a>), LALRAction<'a>>,
    initial_state: usize,
    terminals: Vec<Symbol<'a>>,
}

impl<'a> LALRAutomaton<'a> {
    fn from_grammar(grammar: &'a Grammar<'a>) -> LALRAutomaton<'a> {
        let lr_aut = grammar.get_lr1_automaton();

        let cores: BTreeSet<Core> = lr_aut.states.iter().map(|s| s.into()).collect();
        let cores: Vec<_> = cores.iter().collect();

        let state_to_core: BTreeMap<_, _> = lr_aut
            .states
            .iter()
            .map(|state| {
                let core_index = cores
                    .iter()
                    .enumerate()
                    .find_map(|(i, c)| {
                        let state_core: Core = state.into();
                        if *c == &state_core { Some(i) } else { None }
                    })
                    .unwrap();
                (state, core_index)
            })
            .collect();

        let mut table = HashMap::new();
        let mut terminals = grammar.terminals.clone();
        terminals.insert(Symbol::End);

        for state in lr_aut.states.iter() {
            for terminal in &terminals {
                let goto = grammar.goto(state, &terminal);
                if !goto.0.is_empty() {
                    let action = LALRAction::Shift(*state_to_core.get(&goto).unwrap());

                    if let Some(old) = table.insert(
                        (*state_to_core.get(&state).unwrap(), terminal.clone()),
                        action.clone(),
                    ) && old != action
                    {
                        panic!("Conflict found! {:?}", old)
                    }
                }
            }

            for nt in &grammar.non_terminals {
                let goto = grammar.goto(state, &nt);
                if !goto.0.is_empty() {
                    let action = LALRAction::Goto(*state_to_core.get(&goto).unwrap());

                    if let Some(old) = table.insert(
                        (*state_to_core.get(&state).unwrap(), nt.clone()),
                        action.clone(),
                    ) && old != action
                    {
                        panic!("Conflict found! {:?}", old)
                    }
                }
            }

            for state in &lr_aut.states {
                for item in &state.0 {
                    for terminal in &terminals {
                        if let Some(reduced) = item.reduce(terminal) {
                            let action = LALRAction::Reduce(reduced);

                            if let Some(old) = table.insert(
                                (*state_to_core.get(&state).unwrap(), terminal.clone()),
                                action.clone(),
                            ) && old != action
                            {
                                panic!("Conflict found! {:?}", old)
                            }
                        }
                    }
                }
            }
        }

        let initial_prod = grammar.productions[0].clone();
        let dot = initial_prod.right.len();

        let accepting_item = LR1Item {
            prod: initial_prod,
            dot,
            look_ahead: Symbol::End,
        };

        let accepting_state = grammar.lr1_closure(&accepting_item);

        table.insert(
            (*state_to_core.get(&accepting_state).unwrap(), Symbol::End),
            LALRAction::Accept,
        );

        LALRAutomaton {
            table,
            initial_state: *state_to_core.get(&lr_aut.initial).unwrap(),
            terminals: terminals.into_iter().collect(),
        }
    }

    fn parse(&self, mut input: Vec<Symbol<'a>>) -> Result<(), ParseError<'a>> {
        let mut state_stack = vec![self.initial_state];
        let mut stack = vec![];

        input.reverse();

        while let Some(input_symbol) = input.last() {
            let current_state = state_stack.last().expect("Empty state stack!");

            let action = self.table.get(&(*current_state, *input_symbol));

            match action {
                Some(LALRAction::Shift(new_state)) => {
                    stack.push(input.pop().unwrap());
                    state_stack.push(*new_state);
                }
                Some(LALRAction::Reduce(production)) => {
                    let to_match = production.right.len();

                    if let Some(_) = stack.strip_suffix(production.right.as_slice()) {
                        stack.truncate(stack.len() - to_match);
                        input.push(production.left);
                        state_stack.truncate(state_stack.len() - to_match);
                    } else {
                        return Err(ParseError::CantReduce(production.clone()));
                    }
                }
                Some(LALRAction::Accept) => return Ok(()),
                Some(LALRAction::Goto(new_state)) => {
                    stack.push(input.pop().unwrap());
                    state_stack.push(*new_state);
                }
                None => {
                    let expected_symbols = self
                        .terminals
                        .iter()
                        .filter(|s| self.table.get(&(*current_state, **s)).is_some())
                        .map(Symbol::clone)
                        .collect();

                    return Err(ParseError::NotExpected((
                        input_symbol.clone(),
                        expected_symbols,
                    )));
                }
            }
        }
        Err(ParseError::EndWhileParsing)
    }
}

#[cfg(test)]
mod tests {
    use crate::static_analyzer::{
        grammar::{Grammar, Symbol},
        lalr::LALRAutomaton,
    };

    #[test]
    fn lalr_automaton() {
        let grammar = "S -> B B\nB -> b B|d";
        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let augmented = parsed_grammar.augment();

        let lalr = LALRAutomaton::from_grammar(&augmented);

        dbg!(&lalr);
        assert_eq!(18, lalr.table.len())
    }

    #[test]
    fn lalr_parse() {
        let grammar = "S -> B B\nB -> b B|d";
        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let augmented = parsed_grammar.augment();

        let lalr = LALRAutomaton::from_grammar(&augmented);

        let should_accept = vec![
            vec![
                Symbol::Terminal("b"),
                Symbol::Terminal("d"),
                Symbol::Terminal("b"),
                Symbol::Terminal("d"),
                Symbol::End,
            ],
            vec![
                Symbol::Terminal("b"),
                Symbol::Terminal("b"),
                Symbol::Terminal("d"),
                Symbol::Terminal("b"),
                Symbol::Terminal("b"),
                Symbol::Terminal("d"),
                Symbol::End,
            ],
        ];

        for input in should_accept {
            assert!(lalr.parse(input).is_ok());
        }

        let not_accepted = lalr.parse(vec![
            Symbol::Terminal("b"),
            Symbol::Terminal("d"),
            Symbol::Terminal("b"),
            Symbol::Terminal("d"),
            Symbol::Terminal("b"),
            Symbol::End,
        ]);

        assert!(not_accepted.is_err());
        let error = not_accepted.unwrap_err();
        assert_eq!(error.to_string(), "Found: 'b' while expecting: <EOF>");

        let not_accepted = lalr.parse(vec![
            Symbol::Terminal("b"),
            Symbol::Terminal("d"),
            Symbol::Terminal("b"),
            Symbol::Terminal("b"),
            Symbol::End,
        ]);

        assert!(not_accepted.is_err());
        let error = not_accepted.unwrap_err();
        assert_eq!(error.to_string(), "Found: <EOF> while expecting: 'b', 'd'");
    }

    #[test]
    fn lalr_parse_adrian() {
        let grammar = "S -> A A\nA -> a A | b";
        let parsed_grammar = Grammar::from_str(grammar).unwrap();
        let augmented = parsed_grammar.augment();

        let lalr = LALRAutomaton::from_grammar(&augmented);
        let should_accept = vec![
            vec![
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::End,
            ],
            vec![
                Symbol::Terminal("a"),
                Symbol::Terminal("a"),
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::End,
            ],
        ];

        for input in should_accept {
            assert!(lalr.parse(input).is_ok());
        }

        let should_not_accept = vec![
            vec![
                Symbol::Terminal("a"),
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::End,
            ],
            vec![
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::Terminal("a"),
                Symbol::Terminal("b"),
                Symbol::End,
            ],
        ];

        for input in should_not_accept {
            assert!(lalr.parse(input).is_err());
        }
    }
}
