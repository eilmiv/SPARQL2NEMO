use std::collections::HashMap;
use crate::state::State;

pub struct SolutionMapping {
    pub predicate: String,
    pub variables: Vec<String>,
}

#[derive(Clone)]
pub struct SolutionExpression {
    pub predicate: String,
    pub variables: Vec<String>,
    pub result_var: String,
}

pub struct SolutionPath {
    pub predicate: String,
    pub start_var: String,
    pub end_var: String,
    variables: Vec<String>,
}

pub struct SolutionMultiMapping {
    pub predicate: String,
    pub variables: Vec<String>,
    pub count_var: String,
}

pub struct SolutionSequence {
    pub predicate: String,
    pub variables: Vec<String>,
    pub count_var: String,
    pub index_var: String,
}

pub trait Solution {
    fn pred(&self) -> &String;
    fn vars(&self) -> &Vec<String>;
}

pub(crate) trait SolutionMulti {
    fn count(&self) -> String;
}

impl Solution for SolutionMapping      { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }
impl Solution for SolutionExpression   { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }
impl Solution for SolutionPath         { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }
impl Solution for SolutionMultiMapping { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }
impl Solution for SolutionSequence     { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }

impl SolutionMulti for SolutionMultiMapping { fn count(&self) -> String { self.count_var.to_string() }}
impl SolutionMulti for SolutionSequence     { fn count(&self) -> String { self.count_var.to_string() }}

impl From<SolutionPath> for SolutionMapping {
    fn from(value: SolutionPath) -> Self {
        SolutionMapping{variables: value.variables, predicate: value.predicate}
    }
}

impl SolutionMultiMapping {
    pub fn new(state: &mut State, predicate: &str, vars: Vec<String>) -> SolutionMultiMapping {
        let count_var = state.count_var();
        let mut variables = vars.clone();
        variables.push(count_var.to_string());
        SolutionMultiMapping{
            predicate: state.predicate(predicate),
            variables,
            count_var,
        }
    }
}

impl SolutionExpression {
    pub fn new(state: &mut State, predicate: &str, vars: Vec<String>) -> SolutionExpression {
        let result_var = state.expr_var();
        let mut variables = vars.clone();
        variables.push(result_var.to_string());
        SolutionExpression{
            predicate: state.predicate(predicate),
            variables,
            result_var,
        }
    }

    pub fn result(&self) -> String {
        self.result_var.to_string()
    }

    pub fn external_vars(&self) -> Vec<String>{
        self.vars().iter().filter(|v| **v != self.result()).map(|s| s.to_string()).collect()
    }
}

impl SolutionPath {
    pub fn new(state: &mut State, predicate: &str, start: Option<String>, end: Option<String>) -> SolutionPath {
        let start_var = match start {
            Some(suffix) if suffix.starts_with("?") => suffix.trim_start_matches("?").to_string(),
            _ => state.var("PATH_START_VAR")
        };
        let end_var = match end {
            Some(suffix) if suffix.starts_with("?") => suffix.trim_start_matches("?").to_string(),
            _ => state.var("PATH_END_VAR")
        };
        SolutionPath{
            predicate: state.predicate(predicate),
            start_var: start_var.to_string(),
            end_var: end_var.to_string(),
            variables: vec![start_var, end_var],
        }
    }

    pub fn start(&self) -> String{
        format!("?{}", self.start_var)
    }

    pub fn end(&self) -> String{
        format!("?{}", self.end_var)
    }
}

pub fn format_solution(solution: &dyn Solution) -> String {
    format_solution_mapped(solution, HashMap::new())
}

pub fn format_solution_mapped(solution: &dyn Solution, map: HashMap<String, String>) -> String{
    let mut result = String::new();
    result.push_str(&solution.pred().to_string());
    result.push('(');
    for (index, term) in solution.vars().iter().enumerate() {
        match map.get(term) {
            Some(s) => result.push_str(s),
            None => {
                result.push('?');
                result.push_str(&term.to_string())
            },
        }

        if index < solution.vars().len() - 1 {
            result.push_str(", ");
        }
    }
    if solution.vars().len() == 0 {
        result.push_str("yes");
    }
    result.push(')');
    result
}

pub fn format_solution_path(solution: &SolutionPath, start: Option<String>, end: Option<String>) -> String {
    let mut map = HashMap::new();
    if let Some(s) = start { map.insert(solution.start_var.clone(), s); }
    if let Some(e) = end { map.insert(solution.end_var.clone(), e); }
    format_solution_mapped(solution, map)
}

pub fn combine_variables(s1: &dyn Solution, s2: &dyn Solution) -> Vec<String> {
    let mut vars: Vec<String> = s1.vars().iter().chain(s2.vars().iter()).map(|s| s.to_string()).collect();
    vars.sort();
    vars.dedup();
    vars
}

pub fn expression_variables(s1: &SolutionExpression, s2: &SolutionExpression) -> Vec<String> {
    expression_vars_n(&vec![s1.clone(), s2.clone()])
}

pub fn expression_vars_n(solutions: &Vec<SolutionExpression>) -> Vec<String> {
    let special_vars: Vec<String> = solutions.iter().map(|s| s.result()).collect();

    let mut vars: Vec<String> = solutions.iter()
        .map(|s| s.vars())
        .flatten()
        .map(|s| s.to_string())
        .filter(|v| !special_vars.contains(v))
        .collect();
    vars.sort();
    vars.dedup();
    vars
}
