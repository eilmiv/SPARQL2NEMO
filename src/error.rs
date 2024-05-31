use spargebra::{ParseError, Query};
use spargebra::algebra::{Expression, Function, GraphPattern, PropertyPathExpression};
use spargebra::term::TermPattern;

#[derive(Debug)]
#[allow(dead_code)]
pub enum TranslateError {
    ParseError(ParseError),
    QueryNotImplemented(Query),
    PatternNotImplemented(GraphPattern),
    MultiPatternNotImplemented(GraphPattern),
    TermNotImplemented(TermPattern),
    ExpressionNotImplemented(Expression),
    InvalidNumberOfArguments(Function, Vec<Expression>),
    FunctionNotImplemented(Function),
    PathNotImplemented(PropertyPathExpression),
    Todo(&'static str),
}

impl From<ParseError> for TranslateError {
    fn from(value: ParseError) -> Self { TranslateError::ParseError(value) }
}
