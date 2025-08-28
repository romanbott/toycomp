#[derive(Debug, PartialEq)]
enum Atom {
    Kleene,
    Concat,
    Or,
    Plus,
    Question,
    OpenParen,
    CloseParen,
    Character(char),
}

impl From<&char> for Atom {
    fn from(value: &char) -> Self {
        match value {
            '*' => Atom::Kleene,
            '+' => Atom::Plus,
            '?' => Atom::Question,
            '|' => Atom::Or,
            '(' => Atom::OpenParen,
            ')' => Atom::CloseParen,
            c => Atom::Character(*c),
        }
    }
}

const OPERATORS: [char; 6] = ['*', '+', '?', '|', '(', ')'];
const UNARY_OPERATORS: [char; 3] = ['*', '+', '?'];

fn is_operator(input: &char) -> bool {
    OPERATORS.contains(input)
}

fn is_unary(input: &char) -> bool {
    UNARY_OPERATORS.contains(input)
}

fn explicit_concat(input: &str) -> Vec<Atom> {
    let mut chars = input.chars().peekable();
    let mut output: Vec<Atom> = Vec::new();

    while let Some(current_char) = chars.next() {
        output.push((&current_char).into());

        if let Some(&next_char) = chars.peek() {
            let should_insert_concat =
                // Case 1: Concatenation of two non-operators (e.g., "ab")
                (!is_operator(&current_char) && !is_operator(&next_char))
                // Case 2: Concatenation after a closing parenthesis (e.g., "(a)b")
                || (current_char == ')' && !is_operator(&next_char))
                // Case 3: Concatenation after a unary operator (e.g., "a*b")
                || (is_unary(&current_char) && !is_operator(&next_char))
                // Case 4: Concatenation of a closing parenthesis and an opening parenthesis (e.g., "(a)(b)")
                || (current_char == ')' && next_char == '(')
                // Case 5: Concatenation of a unary operator and an opening parenthesis (e.g., "a*(b)")
                || (is_unary(&current_char) && next_char == '(');

            if should_insert_concat {
                output.push(Atom::Concat);
            }
        }
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_or() {
        let input = "a|b";
        let expected = vec![Atom::Character('a'), Atom::Or, Atom::Character('b')];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }
    #[test]
    fn test_basic_concat() {
        let input = "ab";
        let expected = vec![Atom::Character('a'), Atom::Concat, Atom::Character('b')];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_basic_concat_after_unary() {
        let input = "a*b";
        let expected = vec![
            Atom::Character('a'),
            Atom::Kleene,
            Atom::Concat,
            Atom::Character('b'),
        ];

        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parens() {
        let input = "(a)(b)";
        let expected = vec![
            Atom::OpenParen,
            Atom::Character('a'),
            Atom::CloseParen,
            Atom::Concat,
            Atom::OpenParen,
            Atom::Character('b'),
            Atom::CloseParen,
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parens_after_unary() {
        let input = "a*(b)";
        let expected = vec![
            Atom::Character('a'),
            Atom::Kleene,
            Atom::Concat,
            Atom::OpenParen,
            Atom::Character('b'),
            Atom::CloseParen,
        ];
        let result = explicit_concat(input);
        assert_eq!(result, expected);
    }
}
