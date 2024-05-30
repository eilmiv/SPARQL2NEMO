use std::collections::HashMap;
use spargebra::algebra::{Expression, Function, GraphPattern};
use spargebra::term::{Literal, NamedNode, NamedNodePattern, TermPattern, TriplePattern, Variable};
use spargebra::Query;
use crate::error::TranslateError;
use crate::error::TranslateError::{ExpressionNotImplemented, FunctionNotImplemented, InvalidNumberOfArguments, MultiPatternNotImplemented, PatternNotImplemented, QueryNotImplemented, TermNotImplemented};
use crate::solutions;
use crate::solutions::{format_solution, Solution, SolutionMapping, SolutionMultiMapping, SolutionMulti, format_solution_mapped, SolutionExpression, expression_variables};
use crate::state::State;

const GRAPH_NAME: &str = "input_graph";

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
    let solution = SolutionExpression::new(state, "or", vars);
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
    let solution = SolutionExpression::new(state, "and", vars);
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
    let solution = SolutionExpression::new(state, "not", inner_bool.external_vars());
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
    let special_vars: Vec<String> = solutions.iter().map(|s| s.result()).collect();

    let mut vars: Vec<String> = solutions.iter()
        .map(|s| s.vars())
        .flatten()
        .map(|s| s.to_string())
        .filter(|v| !special_vars.contains(v))
        .collect();
    vars.sort();
    vars.dedup();

    let solution = SolutionExpression::new(state, func.to_lowercase().as_str(), vars);

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
            Function::SubStr => translate_binary_function(state, left, right, binding, "substr", ("SUBSTR(", ", ", ")")),
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
        Expression::FunctionCall(func, params) => translate_function(state, func, params, binding),
        _ => Err(ExpressionNotImplemented(expression.clone()))
    }
}

const TRUE: &'static str = "\"true\"^^<http://www.w3.org/2001/XMLSchema#boolean>";
const FALSE: &'static str = "\"false\"^^<http://www.w3.org/2001/XMLSchema#boolean>";

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
        Expression::In(_, _) |
        Expression::Not(_) | Expression::Or(_, _) | Expression::And(_, _) |
        Expression::FunctionCall(Function::IsBlank, _) |
        Expression::FunctionCall(Function::IsNumeric, _) |
        Expression::FunctionCall(Function::IsIri, _) |
        Expression::FunctionCall(Function::IsLiteral, _) => Ok(inner),
        _ => translate_effective_boolean_value(state, &inner)
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
    let solution_str = solutions::format_solution(&solution);
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
    let variables = solutions::combine_variables(&left_solution, &right_solution);
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
    let variables = solutions::combine_variables(&left_solution, &right_solution);
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
    let expr_solution = translate_expression(state, expression, &inner_solution)?;
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
        GraphPattern::Project{inner, variables} => translate_project(state, inner, variables),
        GraphPattern::Join {left, right} => translate_join(state, left, right),
        GraphPattern::Distinct {inner} => translate_distinct(state, inner),
        GraphPattern::Union {left, right} => translate_union(state, left, right),
        GraphPattern::Filter {expr, inner} => translate_filter(state, expr, inner),
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
    let solution_body = format_solution(&solution);
    for var in inner_solution.vars() {
        state.add_line(format!("{to_describe}(?{var}) :- {body}"));
    }
    state.add_line(format!("{solution_body} :- {GRAPH_NAME}(?s, ?p, ?o), {to_describe}(?s)"));
    Ok(solution)
}

fn translate_query(state: &mut State, query: &Query) -> Result<Box<dyn Solution>, TranslateError>{
    match query {
        Query::Select {pattern: GraphPattern::Distinct{inner}, dataset: _, base_iri: _} => Ok(Box::new(translate_pattern(state, inner)?)),
        Query::Select {pattern, dataset: _, base_iri: _} => Ok(Box::new(translate_pattern_multi(state, pattern)?)),
        Query::Describe {pattern, dataset: _, base_iri: _} => Ok(Box::new(translate_describe(state, pattern)?)),
        _ => Err(QueryNotImplemented(query.clone()))
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
