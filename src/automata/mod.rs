use std::collections::VecDeque;

mod shunting_yard;
use shunting_yard::{Atom, regex_to_atoms};

#[derive(Clone, Copy, Debug)]
enum Arrow {
    Empty(usize),
    Labeled((char, usize)),
}

impl Arrow {
    fn move_target(&self, shift: usize) -> Arrow {
        match self {
            Arrow::Empty(t) => Arrow::Empty(t + shift),
            Arrow::Labeled((l, t)) => Arrow::Labeled((*l, t + shift)),
        }
    }

    fn empty(&self) -> Option<usize> {
        match self {
            Arrow::Empty(t) => Some(*t),
            Arrow::Labeled(_) => None,
        }
    }

    fn accept(&self, char: &char) -> Option<usize> {
        match self {
            Arrow::Empty(_) => None,
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

#[derive(Debug, Clone)]
struct Automaton {
    trans: Vec<Vec<Arrow>>,
    starting: usize,
    final_state: usize,
}

fn join(left: &Automaton, right: &Automaton) -> Automaton {
    let new_trans = [
        left.trans.clone(),
        right
            .trans
            .iter()
            .map(|row| {
                row.iter()
                    .map(|arrow| arrow.move_target(left.trans.len()))
                    .collect()
            })
            .collect(),
    ]
    .concat();

    Automaton {
        trans: new_trans,
        starting: left.starting,
        final_state: right.final_state + left.trans.len(),
    }
}

fn kleene(automaton: &Automaton) -> Automaton {
    let mut automaton = automaton.clone();
    let old_len = automaton.trans.len();

    automaton.trans[automaton.final_state].push(Arrow::Empty(old_len));

    automaton.trans.push(vec![Arrow::Empty(automaton.starting)]);

    automaton.starting = automaton.trans.len() - 1;
    automaton.final_state = automaton.trans.len() - 1;
    automaton
}

fn positive_clousure(automaton: &Automaton) -> Automaton {
    let mut automaton = automaton.clone();

    automaton.trans[automaton.final_state].push(Arrow::Empty(automaton.starting));

    automaton
}

fn zero_or_one(automaton: &Automaton) -> Automaton {
    let mut automaton = automaton.clone();

    automaton.trans[automaton.starting].push(Arrow::Empty(automaton.final_state));

    automaton
}

fn or(left: &Automaton, right: &Automaton) -> Automaton {
    let mut joined = join(left, right);

    let left_len = left.trans.len();
    let joined_len = joined.trans.len();
    joined.starting = joined_len;
    joined.final_state = joined_len + 1;

    joined.trans[joined_len - 1].push(Arrow::Empty(joined.final_state));
    joined.trans[left.final_state].push(Arrow::Empty(joined.final_state));

    joined.trans.push(vec![
        Arrow::Empty(left.starting),
        Arrow::Empty(right.starting + left_len),
    ]);
    joined.trans.push(vec![]);

    joined
}

fn concat(left: &Automaton, right: &Automaton) -> Automaton {
    let mut joined = join(left, right);

    joined.trans[left.final_state].push(Arrow::Empty(right.starting + left.trans.len()));

    joined
}

impl Automaton {
    fn from_char(c: char) -> Automaton {
        Automaton {
            trans: vec![vec![Arrow::Labeled((c, 1))], vec![]],
            starting: 0,
            final_state: 1,
        }
    }

    pub fn from_regex(regex: &str) -> Automaton {
        Automaton::from_atoms(regex_to_atoms(regex))
    }

    fn from_atoms(atoms: VecDeque<Atom>) -> Automaton {
        let mut automatons: Vec<Automaton> = vec![];

        for atom in atoms {
            match atom {
                Atom::Kleene => {
                    let last = automatons.pop().unwrap();
                    automatons.push(kleene(&last));
                }
                Atom::Concat => {
                    let first = automatons.pop().unwrap();
                    let second = automatons.pop().unwrap();
                    automatons.push(concat(&second, &first));
                }
                Atom::Or => {
                    let first = automatons.pop().unwrap();
                    let second = automatons.pop().unwrap();
                    automatons.push(or(&second, &first));
                }
                Atom::Character(c) => automatons.push(Automaton::from_char(c)),
                Atom::Plus => {
                    let last = automatons.pop().unwrap();
                    automatons.push(positive_clousure(&last));
                }
                Atom::Question => {
                    let last = automatons.pop().unwrap();
                    automatons.push(zero_or_one(&last));
                }
                Atom::OpenParen => unreachable!(),
                Atom::CloseParen => unreachable!(),
            }
        }

        automatons.pop().unwrap()
    }

    fn simulate_non_empty_step(&self, states: Vec<usize>, char: char) -> Vec<usize> {
        states
            .iter()
            .flat_map(|state| {
                self.trans[*state]
                    .iter()
                    .filter_map(|arrow| arrow.accept(&char))
            })
            .collect()
    }

    // TODO: optimize
    fn empty_closure(&self, mut states: Vec<usize>) -> Vec<usize> {
        loop {
            let mut new_seen = false;

            for state in states.clone() {
                for new_state in self.trans[state].iter().filter_map(|arrow| arrow.empty()) {
                    if !states.contains(&new_state) {
                        new_seen = true;
                        states.push(new_state);
                    }
                }
            }

            if !new_seen {
                return states;
            }
        }
    }

    fn accept(&self, input: &str) -> bool {
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
            trans: vec![vec![arrow], vec![]],
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
            trans: vec![vec![a_arrow], vec![b_arrow], vec![]],
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
            trans: vec![vec![a_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };
        let aut2 = Automaton {
            trans: vec![vec![b_arrow], vec![]],
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
            trans: vec![vec![a_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };
        let aut2 = Automaton {
            trans: vec![vec![b_arrow], vec![]],
            starting: 0,
            final_state: 1,
        };

        let aut = or(&aut1, &aut2);

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

        let ab_or_c = or(&ab, &c);

        assert!(ab.accept("ab"));
        assert!(ab_or_c.accept("ab"));
        assert!(ab_or_c.accept("c"));
    }

    #[test]
    fn multi_concat() {
        let a = Automaton::from_char('a');

        let mut aut = Automaton {
            trans: vec![],
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

        let aut = zero_or_one(&a);

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
