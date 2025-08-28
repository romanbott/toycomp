use std::collections::VecDeque;

mod shunting_yard;
use shunting_yard::{RegexToken, regex_to_atoms};

/// Represents a transition in a Non-deterministic Finite Automaton (NFA).
///
/// An `Arrow` can be either an epsilon transition (`Epsilon`), which requires no input,
/// or a labeled transition (`Labeled`), which requires a specific character to move to the next state.
#[derive(Clone, Copy, Debug)]
enum Arrow {
    Epsilon(usize),
    Labeled((char, usize)),
}

impl Arrow {
    /// Shifts the target state of the arrow by a given amount.
    /// This is used when combining automata to adjust state indices.
    fn move_target(&self, shift: usize) -> Arrow {
        match self {
            Arrow::Epsilon(t) => Arrow::Epsilon(t + shift),
            Arrow::Labeled((l, t)) => Arrow::Labeled((*l, t + shift)),
        }
    }

    /// Returns the target state if the arrow is an empty transition.
    fn epsilon(&self) -> Option<usize> {
        match self {
            Arrow::Epsilon(t) => Some(*t),
            Arrow::Labeled(_) => None,
        }
    }

    /// Returns the target state if the arrow is a labeled transition and the
    /// given character matches the label.
    fn accept(&self, char: &char) -> Option<usize> {
        match self {
            Arrow::Epsilon(_) => None,
            Arrow::Labeled((l, t)) => {
                if l == char {
                    Some(*t)
                } else {
                    None
                }
            }
        }
    }
}

/// Represents a Non-deterministic Finite Automaton (NFA).
///
/// The automaton is defined by a table of transitions, the starting state, and the final state.
#[derive(Debug, Clone)]
pub struct Automaton {
    /// Table of transitions, each row represents a state.
    table: Vec<Vec<Arrow>>,
    starting: usize,
    final_state: usize,
}

/// Utility function to append the tables of two NFAs.
///
/// The states of the `right` automaton are shifted to avoid conflicts with the
/// `left` automaton's states.
fn append_nfas(left: &Automaton, right: &Automaton) -> Automaton {
    let new_table = [
        left.table.clone(),
        right
            .table
            .iter()
            .map(|row| {
                row.iter()
                    .map(|arrow| arrow.move_target(left.table.len()))
                    .collect()
            })
            .collect(),
    ]
    .concat();

    Automaton {
        table: new_table,
        starting: left.starting,
        final_state: right.final_state + left.table.len(),
    }
}

/// Applies the Kleene star operator (`*`) to an automaton.
///
/// Creates a new NFA that accepts zero or more repetitions of the language
/// accepted by the original automaton.
fn kleene(automaton: &Automaton) -> Automaton {
    let mut automaton = automaton.clone();
    let old_len = automaton.table.len();

    // Add epsilon transition from the old final state to the new final state
    automaton.table[automaton.final_state].push(Arrow::Epsilon(old_len));

    // Add epsilon transition from the new start state to the old start state
    automaton.table.push(vec![Arrow::Epsilon(automaton.starting)]);

    // Update start and final states to the new ones
    automaton.starting = old_len;
    automaton.final_state = old_len;
    automaton
}

/// Applies the positive closure operator (`+`) to an automaton.
///
/// Creates a new NFA that accepts one or more repetitions of the language
/// accepted by the original automaton.
fn positive_clousure(automaton: &Automaton) -> Automaton {
    let mut automaton = automaton.clone();

    // Add an epsilon transition from the final state back to the starting state
    automaton.table[automaton.final_state].push(Arrow::Epsilon(automaton.starting));

    automaton
}

/// Applies the optionality operator (`?`) to an automaton.
///
/// Creates a new NFA that accepts zero or one occurrence of the language
/// accepted by the original automaton.
fn optional(automaton: &Automaton) -> Automaton {
    let mut automaton = automaton.clone();

    // Add an epsilon transition from the starting state to the final state
    automaton.table[automaton.starting].push(Arrow::Epsilon(automaton.final_state));

    automaton
}

/// Applies the union operator (`|`) to two automata.
///
/// Creates a new NFA that accepts the union of the languages accepted by the
/// two original automata.
fn union(left: &Automaton, right: &Automaton) -> Automaton {
    let mut joined = append_nfas(left, right);

    let left_len = left.table.len();
    let joined_len = joined.table.len();
    joined.starting = joined_len;
    joined.final_state = joined_len + 1;

    // Add epsilon transitions from old final states to the new final state
    joined.table[joined_len - 1].push(Arrow::Epsilon(joined.final_state));
    joined.table[left.final_state].push(Arrow::Epsilon(joined.final_state));

    // Add epsilon transitions from the new start state to the old start states
    joined.table.push(vec![
        Arrow::Epsilon(left.starting),
        Arrow::Epsilon(right.starting + left_len),
    ]);

    // Add final state
    joined.table.push(vec![]);

    joined
}

/// Applies the concatenation operator to two automata.
///
/// Creates a new NFA that accepts the language formed by concatenating the
/// languages accepted by the two original automata.
fn concat(left: &Automaton, right: &Automaton) -> Automaton {
    let mut joined = append_nfas(left, right);

    // Add an epsilon transition from the first automaton's final state to the
    // second automaton's start state.
    joined.table[left.final_state].push(Arrow::Epsilon(right.starting + left.table.len()));

    joined
}

impl Automaton {
    /// Creates a new NFA that accepts a single character.
    fn from_char(c: char) -> Automaton {
        Automaton {
            table: vec![vec![Arrow::Labeled((c, 1))], vec![]],
            starting: 0,
            final_state: 1,
        }
    }

    /// Creates an NFA from a regular expression string by first converting the
    /// regex to a sequence of `Atom`s using the Shunting-yard algorithm.
    pub fn from_regex(regex: &str) -> Automaton {
        Automaton::from_atoms(regex_to_atoms(regex))
    }

    /// Constructs an NFA from a sequence of `Atom`s in postfix notation.
    /// This is the core of Thompson's construction.
    // TODO: Improve error handling, remove `unwraps` and `unreachables`
    fn from_atoms(atoms: VecDeque<RegexToken>) -> Automaton {
        let mut automatons: Vec<Automaton> = vec![];

        for atom in atoms {
            match atom {
                RegexToken::Kleene => {
                    let last = automatons.pop().unwrap();
                    automatons.push(kleene(&last));
                }
                RegexToken::Concat => {
                    let first = automatons.pop().unwrap();
                    let second = automatons.pop().unwrap();
                    automatons.push(concat(&second, &first));
                }
                RegexToken::Union => {
                    let first = automatons.pop().unwrap();
                    let second = automatons.pop().unwrap();
                    automatons.push(union(&second, &first));
                }
                RegexToken::Character(c) => automatons.push(Automaton::from_char(c)),
                RegexToken::PositiveClosure => {
                    let last = automatons.pop().unwrap();
                    automatons.push(positive_clousure(&last));
                }
                RegexToken::Optional => {
                    let last = automatons.pop().unwrap();
                    automatons.push(optional(&last));
                }
                // This should not ocurr, since the Shunting Yard algorithm
                // removes parens.
                // TODO: Improve error handling
                RegexToken::OpenParen => unreachable!(),
                RegexToken::CloseParen => unreachable!(),
            }
        }

        automatons.pop().unwrap()
    }

    /// Simulates one step of the NFA, moving from the current set of states
    /// based on a single character input. Epsilon transitions are not followed.
    fn simulate_non_empty_step(&self, states: Vec<usize>, char: char) -> Vec<usize> {
        states
            .iter()
            .flat_map(|state| {
                self.table[*state]
                    .iter()
                    .filter_map(|arrow| arrow.accept(&char))
            })
            .collect()
    }

    /// Computes the epsilon closure of a set of states.
    ///
    /// This finds all states reachable from the initial set of states by following
    /// only epsilon transitions.
    // TODO: optimize
    fn empty_closure(&self, mut states: Vec<usize>) -> Vec<usize> {
        loop {
            let mut new_seen = false;

            for state in states.clone() {
                for new_state in self.table[state].iter().filter_map(|arrow| arrow.epsilon()) {
                    if !states.contains(&new_state) {
                        new_seen = true;
                        states.push(new_state);
                    }
                }
            }

            // loop ends when no new states where added in the last step
            if !new_seen {
                return states;
            }
        }
    }

    /// Determines if the automaton accepts a given input string.
    ///
    /// The simulation proceeds by iteratively calculating the epsilon closure
    /// and then performing a character-based step for each character in the input.
    pub fn accept(&self, input: &str) -> bool {
        let mut states = vec![self.starting];

        for char in input.chars() {
            states = self.empty_closure(states);
            states = self.simulate_non_empty_step(states, char);
        }
        states = self.empty_closure(states);

        states.contains(&self.final_state)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_char_a() {
        let arrow = Arrow::Labeled(('a', 1));
        let aut = Automaton {
            table: vec![vec![arrow], vec![]],
            starting: 0,
            final_state: 1,
        };

        assert!(aut.accept(&"a"));
        assert!(!aut.accept(&"b"));
        assert!(!aut.accept(&"ab"));
    }

    #[test]
    fn test_ab() {
        let a_arrow = Arrow::Labeled(('a', 1));
        let b_arrow = Arrow::Labeled(('b', 2));
        let aut = Automaton {
            table: vec![vec![a_arrow], vec![b_arrow], vec![]],
            starting: 0,
            final_state: 2,
        };

        assert!(!aut.accept(&"a"));
        assert!(!aut.accept(&"b"));
        assert!(aut.accept(&"ab"));
    }

    #[test]
    fn test_concat() {
        let a_arrow = Arrow::Labeled(('a', 1));
        let b_arrow = Arrow::Labeled(('b', 1));
        let aut1 = Automaton {
            table: vec![vec![a_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };
        let aut2 = Automaton {
            table: vec![vec![b_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };

        let aut = concat(&aut1, &aut2);

        assert!(!aut.accept(&"a"));
        assert!(!aut.accept(&"b"));
        assert!(aut.accept(&"ab"));
    }

    #[test]
    fn test_or() {
        let a_arrow = Arrow::Labeled(('a', 1));
        let b_arrow = Arrow::Labeled(('b', 1));
        let aut1 = Automaton {
            table: vec![vec![a_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };
        let aut2 = Automaton {
            table: vec![vec![b_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };

        let aut = union(&aut1, &aut2);

        dbg!(&aut);

        assert!(aut.accept(&"a"));
        assert!(aut.accept(&"b"));
        assert!(!aut.accept(&"ab"));
        assert!(!aut.accept(&"c"));
    }

    #[test]
    fn single_char() {
        let a = Automaton::from_char('a');
        let b = Automaton::from_char('b');

        assert!(a.accept("a"));
        assert!(!a.accept("b"));
        assert!(!b.accept("a"));
        assert!(b.accept("b"));
    }

    #[test]
    fn concat_and_or() {
        let a = Automaton::from_char('a');
        let b = Automaton::from_char('b');
        let c = Automaton::from_char('c');

        let ab = concat(&a, &b);

        let ab_or_c = union(&ab, &c);

        assert!(ab.accept("ab"));
        assert!(ab_or_c.accept("ab"));
        assert!(ab_or_c.accept("c"));
    }

    #[test]
    fn multi_concat() {
        let a = Automaton::from_char('a');

        let mut aut = Automaton {
            table: vec![],
            starting: 0,
            final_state: 0,
        };
        for _ in 0..5 {
            aut = concat(&aut, &a);
        }

        assert!(aut.accept("aaaaa"));
        assert!(!aut.accept("aaaa"));
        assert!(!aut.accept("aaaaaa"));
    }

    #[test]
    fn test_kleene() {
        let a = Automaton::from_char('a');

        let a_kleene = kleene(&a);

        assert!(a_kleene.accept(""));
        assert!(a_kleene.accept("a"));
        assert!(a_kleene.accept("aa"));
        assert!(a_kleene.accept("aaaaaaa"));
        assert!(!a_kleene.accept("ab"));
    }

    #[test]
    fn test_positive_clousure() {
        let a = Automaton::from_char('a');

        let aut = positive_clousure(&a);

        assert!(!aut.accept(""));
        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
        assert!(aut.accept("aaaaaaa"));
        assert!(!aut.accept("ab"));
    }

    #[test]
    fn test_zero_or_one() {
        let a = Automaton::from_char('a');

        let aut = optional(&a);

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(!aut.accept("aa"));
        assert!(!aut.accept("aaaaaaa"));
        assert!(!aut.accept("ab"));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_automaton_from_atoms() {
        let aut = Automaton::from_atoms(regex_to_atoms("a*|b"));

        assert!(aut.accept(""));
        assert!(aut.accept("b"));
        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
    }

    #[test]
    fn test_automaton_from_regex() {
        let aut = Automaton::from_regex("((a*|b)c)*");

        assert!(aut.accept(""));
        assert!(aut.accept("bc"));
        assert!(aut.accept("aaaac"));
        assert!(aut.accept("aaaacbc"));
        assert!(!aut.accept("aa"));
    }
}

#[cfg(test)]
mod tests_adrian {

    use super::*;

    #[test]
    fn test_plus() {
        let aut = Automaton::from_regex("a+");

        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
        assert!(aut.accept("aaaa"));
        assert!(!aut.accept(""));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_optional() {
        let aut = Automaton::from_regex("a?");

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(!aut.accept("aa"));
        assert!(!aut.accept("b"));
    }

    #[test]
    fn test_union() {
        let aut = Automaton::from_regex("a|b");

        assert!(aut.accept("a"));
        assert!(aut.accept("b"));
        assert!(!aut.accept(""));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ab"));
    }

    #[test]
    fn test_precedence_concat_over_union() {
        let aut = Automaton::from_regex("ab|c");

        assert!(aut.accept("ab"));
        assert!(aut.accept("c"));
        assert!(!aut.accept("a"));
        assert!(!aut.accept("b"));
        assert!(!aut.accept("ac"));
    }

    #[test]
    fn test_precedence_kleen_over_concat() {
        let aut = Automaton::from_regex("ab*c");

        assert!(aut.accept("ac"));
        assert!(aut.accept("abc"));
        assert!(aut.accept("abbbc"));
        assert!(!aut.accept("a"));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ab"));
        assert!(!aut.accept("bc"));
    }

    #[test]
    fn test_grouping_kleene() {
        let aut = Automaton::from_regex("(a|b)*");

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(aut.accept("b"));
        assert!(aut.accept("aa"));
        assert!(aut.accept("bb"));
        assert!(aut.accept("ab"));
        assert!(aut.accept("ba"));
        assert!(aut.accept("bababa"));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ac"));
        assert!(!aut.accept("bc"));
    }

    #[test]
    fn test_concat_with_group_union() {
        let aut = Automaton::from_regex("a(b|c)d");

        assert!(aut.accept("abd"));
        assert!(aut.accept("acd"));
        assert!(!aut.accept("ad"));
        assert!(!aut.accept("abcd"));
        assert!(!aut.accept("abd d"));
    }

    #[test]
    fn test_complex_nesting() {
        let aut = Automaton::from_regex("a(b*|c+)?d");

        assert!(aut.accept("ad"));
        assert!(aut.accept("abd"));
        assert!(aut.accept("abbbd"));
        assert!(aut.accept("acd"));
        assert!(aut.accept("acccd"));
        assert!(!aut.accept("a c d"));
        assert!(!aut.accept("abcd"));
        assert!(!aut.accept("abbc"));
    }

    #[test]
    fn test_nested_kleene() {
        let aut = Automaton::from_regex("(a*)*");

        assert!(aut.accept(""));
        assert!(aut.accept("a"));
        assert!(aut.accept("aa"));
        assert!(!aut.accept("b"));
    }


    #[test]
    fn test_optional_inside_concat() {
        let aut = Automaton::from_regex("a(b?)c");

        assert!(aut.accept("ac"));
        assert!(aut.accept("abc"));
        assert!(!aut.accept("a"));
        assert!(!aut.accept("c"));
        assert!(!aut.accept("ab"));
        assert!(!aut.accept("bc"));
    }

    #[test]
    fn test_contains_at_least_one_a() {
        let aut = Automaton::from_regex("(a|b)*a(a|b)*");

        let accepted = ["a", "aa", "ab", "ba", "bab", "bbaabb"];
        let rejected = ["", "b", "bb", "bbbb"];

        for input in accepted {
            assert!(aut.accept(input));
        }
        for input in rejected {
            assert!(!aut.accept(input));
        }
    }
}
