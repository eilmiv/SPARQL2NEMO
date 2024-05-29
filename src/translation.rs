use spargebra::algebra::GraphPattern;
use spargebra::term::{NamedNodePattern, TermPattern, TriplePattern, Variable};
use spargebra::Query;
use crate::error::TranslateError;
use crate::error::TranslateError::{PatternNotImplemented, QueryNotImplemented, TermNotImplemented};
use crate::solutions;
use crate::solutions::{Solution, SolutionMapping};
use crate::state::State;

fn translate_triple(triple: &TriplePattern, variables: &mut Vec<String>) -> Result<String, TranslateError> {
    let mut graph_match = "input_graph(".to_string();
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

fn translate_pattern(state: &mut State, pattern: &GraphPattern) -> Result<SolutionMapping, TranslateError>{
    match pattern {
        GraphPattern::Bgp{patterns} => {translate_bgp(state, patterns)},
        GraphPattern::Project{inner, variables} => {translate_project(state, inner, variables)},
        GraphPattern::Join {left, right} => {translate_join(state, left, right)}
        _ => Err(PatternNotImplemented(pattern.clone()))
    }
}

fn translate_query(state: &mut State, query: &Query) -> Result<SolutionMapping, TranslateError>{
    match query {
        Query::Select {pattern, dataset: _, base_iri: _} => translate_pattern(state, pattern),
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
