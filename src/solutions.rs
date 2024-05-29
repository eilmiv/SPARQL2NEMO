pub struct SolutionMapping {
    pub predicate: String,
    pub variables: Vec<String>,
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

trait SolutionMulti {
    fn count(&self) -> &String;
}

impl Solution for SolutionMapping      { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }

impl Solution for SolutionMultiMapping { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }

impl Solution for SolutionSequence     { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }

impl SolutionMulti for SolutionMultiMapping { fn count(&self) -> &String { &self.count_var }}

impl SolutionMulti for SolutionSequence     { fn count(&self) -> &String { &self.count_var }}

pub fn format_solution(solution: &dyn Solution) -> String {
    let mut result = String::new();
    result.push_str(&solution.pred().to_string());
    result.push('(');
    for (index, term) in solution.vars().iter().enumerate() {
        result.push('?');
        result.push_str(&term.to_string());

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
