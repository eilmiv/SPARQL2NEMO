/// this is just an idea, see basic_solution.rs for current implementation

use std::rc::Rc;
use spargebra::term::Variable;

#[allow(dead_code)]
#[derive(Debug)]
pub struct Column {
    /// prefix for human readable unique names
    pub kind: String,
    /// for columns that are tied to SPARQL Variables
    pub variable: Option<Variable>,
}

#[allow(dead_code)]
impl Column {
    pub fn new(kind: &str) -> Column {
        Column{kind: kind.to_string(), variable: None}
    }
}

#[allow(dead_code)]
impl From<Variable> for Column {
    fn from(value: Variable) -> Self {
        Column{kind: "var".to_string(), variable: Some(value)}
    }
}

#[allow(dead_code)]
pub struct Predicate {
    /// prefix for human readable unique names
    kind: String,
    columns: Vec<Rc<Column>>
}

