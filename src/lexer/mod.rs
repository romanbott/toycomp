pub struct Pattern {
    pub regex: String,
    pub tag: String,
}

pub struct Lexer {
    pub patterns: Vec<Pattern>
}
