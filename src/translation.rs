use std::collections::HashMap;
use spargebra::algebra::{Expression, GraphPattern};
use spargebra::term::{NamedNodePattern, TermPattern, TriplePattern, Variable};
use spargebra::Query;
use crate::error::TranslateError;
use crate::error::TranslateError::{MultiPatternNotImplemented, PatternNotImplemented, QueryNotImplemented, TermNotImplemented};
use crate::solutions;
use crate::solutions::{format_solution, Solution, SolutionMapping, SolutionMultiMapping, SolutionMulti, format_solution_mapped};
use crate::state::State;

const GRAPH_NAME: &str = "input_graph";

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

fn translate_pattern(state: &mut State, pattern: &GraphPattern) -> Result<SolutionMapping, TranslateError>{
    match pattern {
        GraphPattern::Bgp{patterns} => translate_bgp(state, patterns),
        GraphPattern::Project{inner, variables} => translate_project(state, inner, variables),
        GraphPattern::Join {left, right} => translate_join(state, left, right),
        GraphPattern::Distinct {inner} => translate_distinct(state, inner),
        GraphPattern::Union {left, right} => translate_union(state, left, right),
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
