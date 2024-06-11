use std::collections::HashMap;
use spargebra::algebra::{Expression, Function, GraphPattern, PropertyPathExpression};
use spargebra::term::{Literal, NamedNode, NamedNodePattern, TermPattern, TriplePattern, Variable};
use spargebra::Query;
use crate::error::TranslateError;
use crate::error::TranslateError::{ExpressionNotImplemented, FunctionNotImplemented, InvalidNumberOfArguments, MultiPatternNotImplemented, PatternNotImplemented, TermNotImplemented};
use crate::basic_solutions;
use crate::basic_solutions::{expression_variables, expression_vars_n, format_solution, format_solution_mapped, format_solution_path, Solution, SolutionExpression, SolutionMapping, SolutionMulti, SolutionMultiMapping, SolutionPath};
use crate::state::State;

const GRAPH_NAME: &str = "input_graph";
const TRUE: &'static str = "\"true\"^^<http://www.w3.org/2001/XMLSchema#boolean>";
const FALSE: &'static str = "\"false\"^^<http://www.w3.org/2001/XMLSchema#boolean>";

fn translate_expression_variable(state: &mut State, var: &Variable, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    let var_str = var.as_str().to_string();
    let solution = SolutionExpression::new(state, "var", vec![var_str.to_string()]);
    let mut map = HashMap::new();
    map.insert(solution.result(), format!("?{var_str}"));
    let head = format_solution_mapped(&solution, map);
    let body = format_solution(binding);
    state.add_line(format!("{head} :- {body}"));
    Ok(solution)
}

fn translate_expression_named_node(state: &mut State, node: &NamedNode) -> Result<SolutionExpression, TranslateError>{
    let node_str = node.to_string();
    let solution = SolutionExpression::new(state, "named_node", vec![]);
    let mut map = HashMap::new();
    map.insert(solution.result(), node_str);
    state.add_line(format_solution_mapped(&solution, map));
    Ok(solution)
}

fn translate_expression_literal(state: &mut State, node: &Literal) -> Result<SolutionExpression, TranslateError>{
    let node_str = node.to_string();
    let solution = SolutionExpression::new(state, "literal", vec![]);
    let mut map = HashMap::new();
    map.insert(solution.result(), node_str);
    state.add_line(format_solution_mapped(&solution, map));
    Ok(solution)
}

fn translate_or(state: &mut State, left: &Expression, right: &Expression, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    let left_solution = translate_expression(state, left, binding)?;
    let right_solution = translate_expression(state, right, binding)?;
    let left_bool = translate_smart_effective_boolean_value(state, left_solution, left)?;
    let right_bool = translate_smart_effective_boolean_value(state, right_solution, right)?;
    let vars = expression_variables(&left_bool, &right_bool);
    let solution = SolutionExpression::new(state, "boolean_or", vars);
    let map = HashMap::from(
        [(solution.result(), format!("OR(?{}, ?{})", left_bool.result(), right_bool.result()))]
    );
    state.add_line(format!("{} :- {}, {}, {}",
                           format_solution_mapped(&solution, map),
        format_solution(binding), format_solution(&left_bool), format_solution(&right_bool)
    ));
    Ok(solution)
}

fn translate_and(state: &mut State, left: &Expression, right: &Expression, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    let left_solution = translate_expression(state, left, binding)?;
    let right_solution = translate_expression(state, right, binding)?;
    let left_bool = translate_smart_effective_boolean_value(state, left_solution, left)?;
    let right_bool = translate_smart_effective_boolean_value(state, right_solution, right)?;
    let vars = expression_variables(&left_bool, &right_bool);
    let solution = SolutionExpression::new(state, "boolean_and", vars);
    let map = HashMap::from(
        [(solution.result(), format!("AND(?{}, ?{})", left_bool.result(), right_bool.result()))]
    );
    state.add_line(format!("{} :- {}, {}, {}",
                           format_solution_mapped(&solution, map),
        format_solution(binding), format_solution(&left_bool), format_solution(&right_bool)
    ));
    Ok(solution)
}

fn translate_not(state: &mut State, inner: &Expression, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    let inner_solution = translate_expression(state, inner, binding)?;
    let inner_bool = translate_smart_effective_boolean_value(state, inner_solution, inner)?;
    let solution = SolutionExpression::new(state, "boolean_not", inner_bool.external_vars());
    let map = HashMap::from(
        [(solution.result(), format!("NOT(?{})", inner_bool.result()))]
    );
    state.add_line(format!("{} :- {}, {}",
                           format_solution_mapped(&solution, map),
        format_solution(binding), format_solution(&inner_bool)
    ));
    Ok(solution)
}

fn translate_in(state: &mut State, val: &Expression, list: &Vec<Expression>, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    let left_solution = translate_expression(state, val, binding)?;
    let mut right_solutions = Vec::new();
    for expr in list {
        right_solutions.push(translate_expression(state, expr, binding)?);
    }
    let special_vars: Vec<String> = right_solutions.iter()
        .map(|s| s.result())
        .chain(
            vec![left_solution.result()].into_iter()
        )
        .collect();

    let mut vars: Vec<String> = right_solutions.iter()
        .map(|s| s.vars())
        .flatten()
        .chain(left_solution.vars())
        .map(|s| s.to_string())
        .filter(|v| !special_vars.contains(v))
        .collect();
    vars.sort();
    vars.dedup();

    let solution = SolutionExpression::new(state, "in", vars);
    let mut false_body = format_solution(binding);
    let binding_body = format_solution(binding);
    let left_body = format_solution(&left_solution);
    let true_head = format_solution_mapped(&solution, HashMap::from([(solution.result(), TRUE.to_string())]));
    let false_head = format_solution_mapped(&solution, HashMap::from([(solution.result(), FALSE.to_string())]));
    let left_result = left_solution.result();

    false_body.push_str(", ");
    false_body.push_str(left_body.as_str());

    for right in right_solutions {
        let right_body = format_solution_mapped(&right, HashMap::from([(right.result(), format!("?{left_result}"))]));
        let right_result = right.result();
        state.add_line(format!("{true_head} :- {binding_body}, {left_body}, {right_body}" ));
        false_body.push_str(", ");
        false_body.push_str(format_solution(&right).as_str());
        false_body.push_str(format!(", ?{left_result} != ?{right_result}").as_str());
    }
    state.add_line(format!("{false_head} :- {false_body}"));
    Ok(solution)
}

fn translate_positive_exists(state: &mut State, pattern: &GraphPattern, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    let inner_solution = translate_pattern(state, pattern)?;
    let vars = inner_solution.vars().iter().map(|s| s.to_string()).filter(|v| binding.vars().contains(v)).collect();
    let solution = SolutionExpression::new(state, "partial_exists", vars);
    let head = format_solution_mapped(&solution, HashMap::from([(solution.result(), TRUE.to_string())]));
    let inner_body = format_solution(&inner_solution);
    let binding_body = format_solution(binding);

    state.add_line(format!("{head} :- {binding_body}, {inner_body}"));

    Ok(solution)
}

fn translate_exists(state: &mut State, pattern: &GraphPattern, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    let partial_exists = translate_positive_exists(state, pattern, binding)?;
    let solution = SolutionExpression::new(state, "exists", partial_exists.external_vars());

    state.add_line(format!(
        "{} :- {}",
        format_solution_mapped(&solution, HashMap::from([(solution.result(), TRUE.to_string())])),
        format_solution(&partial_exists),
    ));
    state.add_line(format!(
        "{} :- {}, ~{}",
        format_solution_mapped(&solution, HashMap::from([(solution.result(), FALSE.to_string())])),
        format_solution(binding),
        format_solution(&partial_exists),
    ));

    Ok(solution)
}

fn translate_if(state: &mut State, condition: &Expression, true_val: &Expression, false_val: &Expression, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    let condition_solution = translate_expression(state, condition, binding)?;
    let condition_bool = translate_smart_effective_boolean_value(state, condition_solution, condition)?;
    let true_solution = translate_expression(state, true_val, binding)?;
    let false_solution = translate_expression(state, false_val, binding)?;
    let solution = SolutionExpression::new(state, "if", expression_vars_n(&vec![condition_bool.clone(), true_solution.clone(), false_solution.clone()]));

    state.add_line(format!(
        "{} :- {}, {}, {}",
        format_solution_mapped(&solution, HashMap::from([(solution.result(), format!("?{}", true_solution.result()))])),
        format_solution(binding),
        format_solution(&true_solution),
        format_solution_mapped(&condition_bool, HashMap::from([(condition_bool.result(), TRUE.to_string())]))
    ));
    state.add_line(format!(
        "{} :- {}, {}, {}",
        format_solution_mapped(&solution, HashMap::from([(solution.result(), format!("?{}", false_solution.result()))])),
        format_solution(binding),
        format_solution(&false_solution),
        format_solution_mapped(&condition_bool, HashMap::from([(condition_bool.result(), FALSE.to_string())]))
    ));
    Ok(solution)
}

fn translate_by_cases(state: &mut State, left: &Expression, right: &Expression, binding: &dyn Solution, predicate: &str, cases: Vec<(&str, &str, &str, &str)>) -> Result<SolutionExpression, TranslateError>{
    let left_solution = translate_expression(state, left, binding)?;
    let right_solution = translate_expression(state, right, binding)?;
    let vars = expression_variables(&left_solution, &right_solution);
    let solution = SolutionExpression::new(state, predicate, vars);

    let body = format_solution(binding);
    let left_body = format_solution(&left_solution);
    let right_body = format_solution(&right_solution);
    let left_var = left_solution.result();
    let right_var = right_solution.result();
    for (result, pre, mid, post) in cases {
        let head = format_solution_mapped(&solution, HashMap::from([(solution.result(), result.to_string())]));
        state.add_line(format!("{head} :- {body}, {left_body}, {right_body}, {pre}?{left_var}{mid}?{right_var}{post}"));
    }

    Ok(solution)
}

fn translate_nary_function(state: &mut State, params: Vec<&Expression>, binding: &dyn Solution, func: &str) -> Result<SolutionExpression, TranslateError>{
    let solution_results: Result<Vec<_>, _> = params.iter().map(|p| translate_expression(state, p, binding)).collect();
    let solutions = solution_results?;
    let solution = SolutionExpression::new(state, func.to_lowercase().as_str(), basic_solutions::expression_vars_n(&solutions));

    let mut body = format_solution(binding);
    for s in &solutions {
        body.push_str(", ");
        body.push_str(format_solution(s).as_str());
    }
    let param_list = solutions.iter().map(|s| s.result()).map(|s| format!("?{s}")).collect::<Vec<String>>().join(", ");
    let head = format_solution_mapped(&solution, HashMap::from([
        (solution.result(), format!("{func}({param_list})"))
    ]));

    state.add_line(format!("{head} :- {body}"));

    Ok(solution)
}

fn translate_binary_function(state: &mut State, left: &Expression, right: &Expression, binding: &dyn Solution, predicate: &str, func: (&str,  &str, &str)) -> Result<SolutionExpression, TranslateError>{
    let left_solution = translate_expression(state, left, binding)?;
    let right_solution = translate_expression(state, right, binding)?;
    let vars = expression_variables(&left_solution, &right_solution);
    let solution = SolutionExpression::new(state, predicate, vars);

    let body = format_solution(binding);
    let left_body = format_solution(&left_solution);
    let right_body = format_solution(&right_solution);
    let left_var = left_solution.result();
    let right_var = right_solution.result();
    let (pre, mid, post) = func;
    let head = format_solution_mapped(&solution, HashMap::from([
        (solution.result(), format!("{pre}?{left_var}{mid}?{right_var}{post}"))
    ]));

    state.add_line(format!("{head} :- {body}, {left_body}, {right_body}"));


    Ok(solution)
}

fn translate_unary_function(state: &mut State, inner: &Expression, binding: &dyn Solution, predicate: &str, func: (&str,  &str)) -> Result<SolutionExpression, TranslateError>{
    let inner_solution = translate_expression(state, inner, binding)?;
    let solution = SolutionExpression::new(state, predicate, inner_solution.external_vars());

    let body = format_solution(binding);
    let inner_body = format_solution(&inner_solution);
    let inner_var = inner_solution.result();
    let (pre, post) = func;
    let head = format_solution_mapped(&solution, HashMap::from([
        (solution.result(), format!("{pre}?{inner_var}{post}"))
    ]));

    state.add_line(format!("{head} :- {body}, {inner_body}"));

    Ok(solution)
}

fn translate_function(state: &mut State, func: &Function, params: &Vec<Expression>, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    match params.as_slice(){
        [inner] => match func {
            Function::Str => translate_unary_function(state, inner, binding, "str", ("STR(", ")")),
            Function::Lang => translate_unary_function(state, inner, binding, "lang", ("LANG(", ")")),
            Function::Datatype => translate_unary_function(state, inner, binding, "datatype", ("DATATYPE(", ")")),
            Function::Abs => translate_unary_function(state, inner, binding, "abs", ("ABS(", ")")),
            Function::Ceil => translate_unary_function(state, inner, binding, "ceil", ("CEIL(", ")")),
            Function::Floor => translate_unary_function(state, inner, binding, "floor", ("FLOOR(", ")")),
            Function::Round => translate_unary_function(state, inner, binding, "round", ("ROUND(", ")")),
            Function::StrLen => translate_unary_function(state, inner, binding, "strlen", ("STRLEN(", ")")),
            Function::UCase => translate_unary_function(state, inner, binding, "ucase", ("UCASE(", ")")),
            Function::LCase => translate_unary_function(state, inner, binding, "lcase", ("LCASE(", ")")),
            Function::IsIri => translate_unary_function(state, inner, binding, "is_iri", ("isIri(", ")")),
            Function::IsBlank => translate_unary_function(state, inner, binding, "is_blank", ("isNull(", ")")),
            Function::IsLiteral => translate_expression(
                state,
                &Expression::Not(
                    Box::new(
                        Expression::Or(
                            Box::new(Expression::FunctionCall(Function::IsIri, params.clone())),
                            Box::new(Expression::FunctionCall(Function::IsBlank, params.clone())),
                        )
                    )
                ),
                binding
            ),
            Function::IsNumeric => translate_unary_function(state, inner, binding, "is_numeric", ("isNumeric(", ")")),
            _ => Err(FunctionNotImplemented(func.clone()))
        },
        [left, right] => match func {
            Function::Str => translate_binary_function(state, left, right, binding, "str", ("CONCAT(", ", ", ")")),
            Function::SubStr => translate_binary_function(state, left, right, binding, "substr", ("SUBSTR(", ", ", " - 1)")),
            Function::Contains => translate_binary_function(state, left, right, binding, "contains", ("CONTAINS(", ", ", ")")),
            Function::StrStarts => translate_binary_function(state, left, right, binding, "str_starts", ("STRSTARTS(", ", ", ")")),
            Function::StrEnds => translate_binary_function(state, left, right, binding, "str_ends", ("STRENDS(", ", ", ")")),
            Function::StrBefore => translate_binary_function(state, left, right, binding, "str_before", ("STRBEFORE(", ", ", ")")),
            Function::StrAfter => translate_binary_function(state, left, right, binding, "str_after", ("STRAFTER(", ", ", ")")),
            _ => Err(FunctionNotImplemented(func.clone()))
        }
        [a, b, c] => match func {
            Function::SubStr => translate_nary_function(
                state,
                vec![a, &Expression::Subtract(Box::new(b.clone()), Box::new(Expression::Literal(Literal::from(1)))), c],
                binding,
                "SUBSTRING"
            ),
            _ => Err(FunctionNotImplemented(func.clone()))
        }
        _ => Err(InvalidNumberOfArguments(func.clone(), params.clone()))
    }
}

fn translate_expression(state: &mut State, expression: &Expression, binding: &dyn Solution) -> Result<SolutionExpression, TranslateError>{
    match expression {
        Expression::Variable(v) => translate_expression_variable(state, v, binding),
        Expression::NamedNode(n) => translate_expression_named_node(state, n),
        Expression::Literal(n) => translate_expression_literal(state, n),
        Expression::Or(left, right) => translate_or(state, left, right, binding),
        Expression::And(left, right) => translate_and(state, left, right, binding),
        Expression::SameTerm(left, right) =>
            translate_by_cases(state, left, right, binding, "same_term", vec![
                (TRUE, "fullStr(", ") = fullStr(", ")"), (FALSE, "fullStr(", ") != fullStr(", ")")
            ]),
        Expression::Greater(left, right) =>
            translate_by_cases(state, left, right, binding, "greater", vec![
                (TRUE, "", " > ", ""), (FALSE, "", " <= ", "")
            ]),
        Expression::GreaterOrEqual(left, right) =>
            translate_by_cases(state, left, right, binding, "greater_equal", vec![
                (TRUE, "", " >= ", ""), (FALSE, "", " < ", "")
            ]),
        Expression::Less(left, right) =>
            translate_by_cases(state, left, right, binding, "less", vec![
                (TRUE, "", " < ", ""), (FALSE, "", " >= ", "")
            ]),
        Expression::LessOrEqual(left, right) =>
            translate_by_cases(state, left, right, binding, "less_equal", vec![
                (TRUE, "", " <= ", ""), (FALSE, "", " > ", "")
            ]),
        Expression::Equal(left, right) =>
            translate_by_cases(state, left, right, binding, "equal", vec![
                (TRUE, "", " = ", ""), (FALSE, "", " != ", "")
            ]),
        Expression::In(left, rights) => translate_in(state, left, rights, binding),
        Expression::Add(left, right) => translate_binary_function(state, left, right, binding, "add", ("", " + ", "")),
        Expression::Subtract(left, right) => translate_binary_function(state, left, right, binding, "subtract", ("", " - ", "")),
        Expression::Multiply(left, right) => translate_binary_function(state, left, right, binding, "multiply", ("", " * ", "")),
        Expression::Divide(left, right) => translate_binary_function(state, left, right, binding, "divide", ("", " / ", "")),
        Expression::UnaryPlus(inner) => translate_unary_function(state, inner, binding, "unary_plus", ("0 + ", "")),
        Expression::UnaryMinus(inner) => translate_unary_function(state, inner, binding, "unary_minus", ("0 - ", "")),
        Expression::Not(inner) => translate_not(state, inner, binding),
        Expression::Exists(inner) => translate_exists(state, inner, binding),
        Expression::If(cond, true_val, false_val) => translate_if(state, cond, true_val, false_val, binding),
        Expression::FunctionCall(func, params) => translate_function(state, func, params, binding),
        _ => Err(ExpressionNotImplemented(expression.clone()))
    }
}

fn translate_effective_boolean_value(state: &mut State, inner: &SolutionExpression) -> Result<SolutionExpression, TranslateError>{
    let inner_var = inner.result();
    let vars = inner.vars().iter().filter(|v| **v != inner_var).map(|v| v.to_string()).collect();
    let solution = SolutionExpression::new(state, "effective_boolean_value", vars);
    let mut true_map = HashMap::new();
    let mut false_map = HashMap::new();
    true_map.insert(solution.result(), TRUE.to_string());
    false_map.insert(solution.result(), FALSE.to_string());
    let true_head = format_solution_mapped(&solution, true_map);
    let false_head = format_solution_mapped(&solution, false_map);
    let body = format_solution(inner);

    // numbers
    state.add_line(format!("{false_head} :- {body}, ?{inner_var} = 0"));
    state.add_line(format!("{true_head} :- {body}, isNumeric(?{inner_var}) = {TRUE}, ?{inner_var} != 0"));

    // strings
    state.add_line(format!("{false_head} :- {body}, STRLEN(?{inner_var}) = 0"));
    state.add_line(format!("{true_head} :- {body}, STRLEN(?{inner_var}) > 0"));

    // bools
    state.add_line(format!("{false_head} :- {body}, ?{inner_var} = {FALSE}"));
    state.add_line(format!("{true_head} :- {body}, ?{inner_var} = {TRUE}"));

    Ok(solution)
}

fn translate_smart_effective_boolean_value(state: &mut State, inner: SolutionExpression, original_expression: &Expression) -> Result<SolutionExpression, TranslateError> {
    match original_expression {
        Expression::Equal(_, _) | Expression::SameTerm(_, _) |
        Expression::Greater(_, _) | Expression::GreaterOrEqual(_, _) |
        Expression::Less(_, _) | Expression::LessOrEqual(_, _) |
        Expression::In(_, _) | Expression::Exists(_) |
        Expression::Not(_) | Expression::Or(_, _) | Expression::And(_, _) |
        Expression::FunctionCall(Function::IsBlank, _) |
        Expression::FunctionCall(Function::IsNumeric, _) |
        Expression::FunctionCall(Function::IsIri, _) |
        Expression::FunctionCall(Function::IsLiteral, _) => Ok(inner),
        _ => translate_effective_boolean_value(state, &inner)
    }
}

fn translate_path_property(state: &mut State, start: Option<String>, property: &NamedNode, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    let solution = SolutionPath::new(state, "path_property", start.clone(), end.clone());
    state.add_line(format!(
        "{} :- {}({}, {}, {})",
        format_solution_path(&solution, start.clone(), end.clone()),
        GRAPH_NAME,
        start.unwrap_or(solution.start()),
        property.to_string(),
        end.unwrap_or(solution.end()),
    ));
    Ok(solution)
}

fn translate_negated_property_set(state: &mut State, start: Option<String>, properties: &Vec<NamedNode>, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    let solution = SolutionPath::new(state, "negated_property_set", start.clone(), end.clone());
    let property_var = state.var("PROPERTY_VAR");
    let mut property_conditions = String::new();
    for p in properties.iter().map(|p| p.to_string()) {
        property_conditions.push_str(&format!(", ?{property_var} != {p}"));
    }

    state.add_line(format!(
        "{} :- {}({}, ?{}, {}){}",
        format_solution_path(&solution, start.clone(), end.clone()),
        GRAPH_NAME,
        start.unwrap_or(solution.start()),
        property_var,
        end.unwrap_or(solution.end()),
        property_conditions,
    ));
    Ok(solution)
}

fn translate_reverse_path(state: &mut State, start: Option<String>, inner: &PropertyPathExpression, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    let inner_solution = translate_path(state, end.clone(), inner, start.clone())?;
    let solution = SolutionPath::new(state, "reverse", start, end);
    state.add_line(format!(
        "{} :- {}",
        format_solution(&solution),
        format_solution_path(&inner_solution, Some(solution.end()), Some(solution.start())),
    ));
    Ok(solution)
}

fn translate_path_sequence(state: &mut State, start: Option<String>, first: &PropertyPathExpression, second: &PropertyPathExpression, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    let first_solution = translate_path(state, start.clone(), first, None)?;
    let second_solution = translate_path(state, None, second, end.clone())?;
    let solution = SolutionPath::new(state, "sequence", start, end);
    state.add_line(format!(
        "{} :- {}, {}",
        format_solution(&solution),
        format_solution_path(&first_solution, Some(solution.start()), None),
        format_solution_path(&second_solution, Some(first_solution.end()), Some(solution.end())),
    ));
    Ok(solution)
}

fn translate_path_alternative(state: &mut State, start: Option<String>, first: &PropertyPathExpression, second: &PropertyPathExpression, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    let first_solution = translate_path(state, start.clone(), first, end.clone())?;
    let second_solution = translate_path(state, start.clone(), second, end.clone())?;
    let solution = SolutionPath::new(state, "alternative", start, end);
    state.add_line(format!(
        "{} :- {}",
        format_solution(&solution),
        format_solution_path(&first_solution, Some(solution.start()), Some(solution.end()))
    ));
    state.add_line(format!(
        "{} :- {}",
        format_solution(&solution),
        format_solution_path(&second_solution, Some(solution.start()), Some(solution.end()))
    ));
    Ok(solution)
}

fn iterate_path(state: &mut State, start: Option<String>, path: &PropertyPathExpression) -> Result<SolutionPath, TranslateError>{
    let inner_solution = translate_path(state, None, path, None)?;
    let solution = SolutionPath::new(state, "path_recursive", start.clone(), None);
    state.add_line(format!(
        "{} :- {}",
        format_solution_path(&solution, start.clone(), None),
        format_solution_path(&inner_solution, start.clone().or(Some(solution.start())).clone(), Some(solution.end())),
    ));
    state.add_line(format!(
        "{} :- {}, {}",
        format_solution_path(&solution, start.clone(), None),
        format_solution_path(&solution, start.clone(), Some(inner_solution.start())),
        format_solution_path(&inner_solution, None, Some(solution.end())),
    ));
    Ok(solution)
}

fn is_term(t: &Option<String>) -> bool {
    match t {
        Some(s) => !s.starts_with('?'),
        None => false,
    }
}

fn zero_path_extend(state: &mut State, solution: &SolutionPath, start: Option<String>, end: Option<String>) {
    // two terms, different
    if is_term(&start) && is_term(&end) && &start != &end { return }

    let start_term = if is_term(&start) { start } else { None };
    let end_term = if is_term(&end) { end } else { None };
    let term = start_term.or(end_term);

    if let Some(t) = term {
        // one term or two terms that are the same
        state.add_line(format_solution_path(&solution, Some(t.clone()), Some(t)));
    }
    else {
        // no terms
        state.add_line(format!(
            "{} :- {}(?s, ?p, ?o)",
            format_solution_path(&solution, Some("?s".to_string()), Some("?s".to_string())),
            GRAPH_NAME
        ));
        state.add_line(format!(
            "{} :- {}(?s, ?p, ?o)",
            format_solution_path(&solution, Some("?o".to_string()), Some("?o".to_string())),
            GRAPH_NAME
        ));
    }
}

fn translate_one_or_more_path(state: &mut State, start: Option<String>, path: &PropertyPathExpression, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    let reverse_iterate = is_term(&end) && !is_term(&start);
    let path_to_iterate = if reverse_iterate {&PropertyPathExpression::Reverse(Box::new(path.clone()))} else {path};
    let inner_start = if reverse_iterate {end.clone()} else {start.clone()};

    let inner_solution = iterate_path(state, inner_start, path_to_iterate)?;
    let solution = SolutionPath::new(state, "one_or_more", start.clone(), end.clone());

    let mut inner_start = Some(solution.start());
    let mut inner_end = Some(solution.end());
    let mut outer_start = Some(solution.start());
    let mut outer_end = Some(solution.end());
    if is_term(&start) { outer_start = start.clone(); inner_start = start };
    if is_term(&end) { outer_end = end.clone(); inner_end = end };
    if reverse_iterate { (inner_end, inner_start) = (inner_start, inner_end) };

    state.add_line(format!(
        "{} :- {}",
        format_solution_path(&solution, outer_start, outer_end),
        format_solution_path(&inner_solution, inner_start, inner_end),
    ));

    Ok(solution)
}

fn translate_zero_or_more_path(state: &mut State, start: Option<String>, path: &PropertyPathExpression, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    let inner_solution = translate_one_or_more_path(state, start.clone(), path, end.clone())?;
    let solution = SolutionPath::new(state, "zero_or_more", start.clone(), end.clone());
    state.add_line(format!(
        "{} :- {}", format_solution(&solution), format_solution_path(&inner_solution, Some(solution.start()), Some(solution.end()))
    ));
    zero_path_extend(state, &solution, start, end);
    Ok(solution)
}

fn translate_zero_or_one_path(state: &mut State, start: Option<String>, path: &PropertyPathExpression, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    let inner_solution = translate_path(state, start.clone(), path, end.clone())?;
    let solution = SolutionPath::new(state, "zero_or_one", start.clone(), end.clone());
    state.add_line(format!(
        "{} :- {}", format_solution(&solution), format_solution_path(&inner_solution, Some(solution.start()), Some(solution.end()))
    ));
    zero_path_extend(state, &solution, start, end);
    Ok(solution)
}

fn translate_path(state: &mut State, start: Option<String>, path: &PropertyPathExpression, end: Option<String>) -> Result<SolutionPath, TranslateError>{
    match path {
        PropertyPathExpression::NamedNode(p) => translate_path_property(state, start, p, end),
        PropertyPathExpression::Reverse(inner) => translate_reverse_path(state, start, inner, end),
        PropertyPathExpression::Sequence(first, second) => translate_path_sequence(state, start, first, second, end),
        PropertyPathExpression::Alternative(a, b) => translate_path_alternative(state, start, a, b, end),
        PropertyPathExpression::OneOrMore(p) => translate_one_or_more_path(state, start, p, end),
        PropertyPathExpression::ZeroOrMore(p) => translate_zero_or_more_path(state, start, p, end),
        PropertyPathExpression::ZeroOrOne(p) => translate_zero_or_one_path(state, start, p, end),
        PropertyPathExpression::NegatedPropertySet(ps) => translate_negated_property_set(state, start, ps, end),
    }
}

fn translate_node(node: &TermPattern) -> Result<String, TranslateError> {
    match node {
        TermPattern::NamedNode(n) => Ok(n.to_string()),
        TermPattern::BlankNode(n) => Ok(format!("?BNODE_VARIABLE_{}", n.as_str())),
        TermPattern::Variable(n) => Ok(n.to_string()),
        _ => Err(TermNotImplemented(node.clone()))
    }
}


fn translate_triple(triple: &TriplePattern, variables: &mut Vec<String>) -> Result<String, TranslateError> {
    let mut graph_match = GRAPH_NAME.to_string();
    graph_match.push_str("(");
    match &triple.subject {
        TermPattern::NamedNode(node) => graph_match.push_str(node.to_string().as_str()),
        TermPattern::BlankNode(node) => {
            let id = node.as_str();
            let var_string = format!("?BNODE_VARIABLE_{id}");
            graph_match.push_str(var_string.as_str());
        },
        TermPattern::Variable(var) => {
            variables.push(var.as_str().to_string());
            graph_match.push_str(var.to_string().as_str());
        }
        _ => return Err(TermNotImplemented(triple.subject.clone()))
    }
    graph_match.push_str(", ");
    match &triple.predicate {
        NamedNodePattern::NamedNode(node) => graph_match.push_str(node.to_string().as_str()),
        NamedNodePattern::Variable(var) => {
            variables.push(var.as_str().to_string());
            graph_match.push_str(var.to_string().as_str());
        }
    }
    graph_match.push_str(", ");
    match &triple.object {
        TermPattern::NamedNode(node) => graph_match.push_str(node.to_string().as_str()),
        TermPattern::Literal(node) => graph_match.push_str(node.to_string().as_str()),
        TermPattern::BlankNode(node) => {
            let id = node.as_str();
            let var_string = format!("?BNODE_VARIABLE_{id}");
            graph_match.push_str(var_string.as_str());
        },
        TermPattern::Variable(var) => {
            variables.push(var.as_str().to_string());
            graph_match.push_str(var.to_string().as_str());
        }
    }
    graph_match.push_str(")");
    Ok(graph_match)
}

fn translate_bgp(state: &mut State, patterns: &Vec<TriplePattern>) -> Result<SolutionMapping, TranslateError>{
    let mut variables = Vec::new();
    let mut body_parts = Vec::new();
    for triple in patterns.iter() {
        body_parts.push(translate_triple(triple, &mut variables)?)
    }
    let body = body_parts.join(", ");
    variables.sort();
    variables.dedup();
    let solution = SolutionMapping{predicate: state.predicate("bgp"), variables};
    let solution_str = basic_solutions::format_solution(&solution);
    state.add_line(format!("{solution_str} :- {body}"));
    Ok(solution)
}

fn translate_project(state: &mut State, pattern: &Box<GraphPattern>, variables: &Vec<Variable>) -> Result<SolutionMapping, TranslateError> {
    let inner_pred = translate_pattern(state, pattern)?;
    let solution = SolutionMapping{predicate: state.predicate("projection"), variables: variables.iter().map(|var| var.as_str().to_string()).collect()};
    state.add_rule(&solution, vec![&inner_pred]);
    Ok(solution)
}

fn translate_join(state: &mut State, left: &Box<GraphPattern>, right: &Box<GraphPattern>) -> Result<SolutionMapping, TranslateError> {
    let left_solution = translate_pattern(state, left)?;
    let right_solution = translate_pattern(state, right)?;
    let variables = basic_solutions::combine_variables(&left_solution, &right_solution);
    let solution = SolutionMapping{predicate: state.predicate("join"), variables};
    state.add_rule(&solution, vec![&left_solution, &right_solution]);
    Ok(solution)
}

fn translate_distinct(state: &mut State, pattern: &GraphPattern) -> Result<SolutionMapping, TranslateError> {
    translate_pattern(state, pattern)
}

fn translate_distinct_multi(state: &mut State, pattern: &GraphPattern) -> Result<SolutionMultiMapping, TranslateError> {
    let inner = translate_pattern(state, pattern)?;
    let solution = SolutionMultiMapping::new(state, "distinct", inner.vars().clone());
    let mut map = HashMap::new();
    map.insert(solution.count(), "1".to_string());
    let head = format_solution_mapped(&solution, map);
    let body = format_solution(&inner);
    state.add_line(format!("{head} :- {body}"));
    Ok(solution)
}

fn translate_union(state: &mut State, left: &Box<GraphPattern>, right: &Box<GraphPattern>) -> Result<SolutionMapping, TranslateError> {
    let left_solution = translate_pattern(state, left)?;
    let right_solution = translate_pattern(state, right)?;
    let variables = basic_solutions::combine_variables(&left_solution, &right_solution);
    let solution = SolutionMapping{predicate: state.predicate("union"), variables};
    let mut left_map = HashMap::new();
    let mut right_map = HashMap::new();
    for var in solution.vars() {
        if !left_solution.vars().contains(var) {
            left_map.insert(var.to_string(), format!("!{var}"));
        }
    }
    for var in solution.vars() {
        if !right_solution.vars().contains(var) {
            right_map.insert(var.to_string(), format!("!{var}"));
        }
    }

    let head_left = format_solution_mapped(&solution, left_map);
    let head_right = format_solution_mapped(&solution, right_map);
    let body_left = format_solution(&left_solution);
    let body_right = format_solution(&right_solution);
    state.add_line(format!("{head_left} :- {body_left}"));
    state.add_line(format!("{head_right} :- {body_right}"));
    Ok(solution)
}

fn translate_filter(state: &mut State, expression: &Expression, inner: &Box<GraphPattern>) -> Result<SolutionMapping, TranslateError> {
    let inner_solution = translate_pattern(state, inner)?;
    let expr_solution = match expression {
        Expression::Exists(pattern) => translate_positive_exists(state, pattern, &inner_solution),
        _ => translate_expression(state, expression, &inner_solution)
    }?;
    let bool_solution = translate_smart_effective_boolean_value(state, expr_solution, expression)?;

    let solution = SolutionMapping{predicate: state.predicate("filter"), variables: inner_solution.vars().clone()};
    let head = format_solution(&solution);
    let body = format_solution(&inner_solution);
    let mut map = HashMap::new();
    map.insert(bool_solution.result(), TRUE.to_string());
    let expr = format_solution_mapped(&bool_solution, map);
    state.add_line(format!("{head} :- {body}, {expr}"));
    Ok(solution)
}

fn translate_pattern(state: &mut State, pattern: &GraphPattern) -> Result<SolutionMapping, TranslateError>{
    match pattern {
        GraphPattern::Bgp{patterns} => translate_bgp(state, patterns),
        GraphPattern::Path {subject, path, object} =>
            Ok(SolutionMapping::from(
                translate_path(
                    state,
                    Some(translate_node(subject)?),
                    path,
                    Some(translate_node(object)?)
                )?
            )),
        GraphPattern::Join {left, right} => translate_join(state, left, right),
        GraphPattern::Filter {expr, inner} => translate_filter(state, expr, inner),
        GraphPattern::Union {left, right} => translate_union(state, left, right),
        GraphPattern::Project{inner, variables} => translate_project(state, inner, variables),
        GraphPattern::Distinct {inner} => translate_distinct(state, inner),
        _ => Err(PatternNotImplemented(pattern.clone()))
    }
}

fn translate_pattern_multi(state: &mut State, pattern: &GraphPattern) -> Result<SolutionMultiMapping, TranslateError>{
    match pattern {
        GraphPattern::Distinct{inner} => { translate_distinct_multi(state, inner) },
        _ => Err(MultiPatternNotImplemented(pattern.clone()))
    }
}

fn translate_describe(state: &mut State, pattern: &GraphPattern) -> Result<SolutionMapping, TranslateError>{
    let inner_solution = translate_pattern(state, pattern)?;
    let body = format_solution(&inner_solution);
    let to_describe = state.predicate("to_describe");
    let solution = SolutionMapping{predicate: state.predicate("description_graph"), variables: vec!["s".to_string(), "p".to_string(), "o".to_string()]};
    let solution_head = format_solution(&solution);
    for var in inner_solution.vars() {
        state.add_line(format!("{to_describe}(?{var}) :- {body}"));
    }
    state.add_line(format!("{solution_head} :- {GRAPH_NAME}(?s, ?p, ?o), {to_describe}(?s)"));
    Ok(solution)
}

fn translate_ask(state: &mut State, pattern: &GraphPattern) -> Result<SolutionMapping, TranslateError>{
    let inner_solution = translate_pattern(state, pattern)?;
    let body = format_solution(&inner_solution);
    let solution = SolutionMapping{predicate: state.predicate("ask_result"), variables: vec!["r".to_string()]};
    let true_head = format_solution_mapped(&solution, HashMap::from([("r".to_string(), TRUE.to_string())]));
    let false_head = format_solution_mapped(&solution, HashMap::from([("r".to_string(), FALSE.to_string())]));

    let dummy = state.predicate("dummy");
    state.add_line(format!("{dummy}(exists)"));
    state.add_line(format!("{true_head} :- {body}"));
    state.add_line(format!("{false_head} :- {dummy}(exists), ~{body}"));
    Ok(solution)
}

fn translate_construct_term(term: &TermPattern) -> String {
    match term {
        TermPattern::NamedNode(n) => n.to_string(),
        TermPattern::Literal(l) => l.to_string(),
        TermPattern::Variable(v) => v.to_string(),
        TermPattern::BlankNode(b) => format!("!BNODE_VARIABLE_{}", b.as_str()),
    }
}

fn translate_construct(state: &mut State, pattern: &GraphPattern, template: &Vec<TriplePattern>) -> Result<SolutionMapping, TranslateError>{
    let inner_solution = translate_pattern(state, pattern)?;
    let body = format_solution(&inner_solution);
    let proto_graph = SolutionMapping{predicate: state.predicate("proto_graph"), variables: vec!["s".to_string(), "p".to_string(), "o".to_string()]};
    let solution = SolutionMapping{predicate: state.predicate("constructed_graph"), variables: vec!["s".to_string(), "p".to_string(), "o".to_string()]};

    let head = template.iter()
        .map(|triple|
            format_solution_mapped(
                &proto_graph, HashMap::from(
                    [
                        ("s".to_string(), translate_construct_term(&triple.subject)),
                        ("p".to_string(), triple.predicate.to_string()),
                        ("o".to_string(), translate_construct_term(&triple.object))
                    ],
                )
            )
        )
        .collect::<Vec<_>>()
        .join(", ");

    state.add_line(format!("{head} :- {body}"));
    state.add_line(format!("{} :- {}, AND(OR(isNull(?s), isIri(?s)), isIri(?p)) = {}", format_solution(&solution), format_solution(&proto_graph), TRUE));
    Ok(solution)
}

fn translate_query(state: &mut State, query: &Query) -> Result<Box<dyn Solution>, TranslateError>{
    match query {
        Query::Select {pattern: GraphPattern::Distinct{inner}, dataset: _, base_iri: _} => Ok(Box::new(translate_pattern(state, inner)?)),
        Query::Select {pattern, dataset: _, base_iri: _} => Ok(Box::new(translate_pattern_multi(state, pattern)?)),
        Query::Describe {pattern, dataset: _, base_iri: _} => Ok(Box::new(translate_describe(state, pattern)?)),
        Query::Ask {pattern, dataset: _, base_iri: _} => Ok(Box::new(translate_ask(state, pattern)?)),
        Query::Construct {pattern, dataset: _, base_iri: _, template} => Ok(Box::new(translate_construct(state, pattern, template)?)),
    }
}

pub fn translate(query_str: &str) -> Result<String, TranslateError> {
    let mut state = State::new();
    let query = Query::parse(query_str, None)?;
    let solution = translate_query(&mut state, &query)?;
    state.add("@output ".to_string());
    state.add(solution.pred().clone());
    state.add(" .".to_string());
    Ok(state.to_string())
}
