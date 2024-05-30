use std::collections::HashMap;
use crate::state::State;

pub struct SolutionMapping {
    pub predicate: String,
    pub variables: Vec<String>,
}

pub struct SolutionExpression {
    pub predicate: String,
    pub variables: Vec<String>,
    pub result_var: String,
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
impl Solution for SolutionMultiMapping { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }
impl Solution for SolutionSequence     { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }

impl SolutionMulti for SolutionMultiMapping { fn count(&self) -> String { self.count_var.to_string() }}
impl SolutionMulti for SolutionSequence     { fn count(&self) -> String { self.count_var.to_string() }}

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

    result.push(')');
    result
}

pub fn combine_variables(s1: &dyn Solution, s2: &dyn Solution) -> Vec<String> {
    let mut vars: Vec<String> = s1.vars().iter().chain(s2.vars().iter()).map(|s| s.to_string()).collect();
    vars.sort();
    vars.dedup();
    vars
}

pub fn expression_variables(s1: &SolutionExpression, s2: &SolutionExpression) -> Vec<String> {
    let mut vars: Vec<String> = s1.vars().iter()
        .chain(s2.vars().iter())
        .map(|s| s.to_string())
        .filter(|v| **v != s1.result() && **v != s2.result())
        .collect();
    vars.sort();
    vars.dedup();
    vars
}
