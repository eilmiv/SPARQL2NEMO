use spargebra::{ParseError, Query};
use spargebra::algebra::GraphPattern;
use spargebra::term::{NamedNodePattern, TermPattern, TriplePattern, Variable};
use crate::TranslateError::{PatternNotImplemented, QueryNotImplemented, TermNotImplemented};


#[derive(Debug)]
#[allow(dead_code)]
enum TranslateError {
    ParseError(ParseError),
    QueryNotImplemented(Query),
    PatternNotImplemented(GraphPattern),
    TermNotImplemented(TermPattern),
    Todo(&'static str),
}

impl From<ParseError> for TranslateError {
    fn from(value: ParseError) -> Self { TranslateError::ParseError(value) }
}

struct SolutionMapping {
    predicate: String,
    variables: Vec<String>,
}

/*struct SolutionMultiMapping {
    predicate: String,
    variables: Vec<String>,
    count_var: String,
}

struct SolutionSequence {
    predicate: String,
    variables: Vec<String>,
    count_var: String,
    index_var: String,
}*/

trait Solution {
    fn pred(&self) -> &String;
    fn vars(&self) -> &Vec<String>;
}

/*trait SolutionMulti {
    fn count(&self) -> &String;
}*/

impl Solution for SolutionMapping      { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }
/*impl Solution for SolutionMultiMapping { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }
impl Solution for SolutionSequence     { fn pred(&self) -> &String { &self.predicate } fn vars(&self) -> &Vec<String> { &self.variables } }
impl SolutionMulti for SolutionMultiMapping { fn count(&self) -> &String { &self.count_var }}
impl SolutionMulti for SolutionSequence     { fn count(&self) -> &String { &self.count_var }}*/

fn format_solution(solution: &dyn Solution) -> String {
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

fn combine_variables(s1: &dyn Solution, s2: &dyn Solution) -> Vec<String> {
    let mut vars: Vec<String> = s1.vars().iter().chain(s2.vars().iter()).map(|s| s.to_string()).collect();
    vars.sort();
    vars.dedup();
    vars
}

#[derive(Debug)]
struct State {
    text: String,
    predicate_names: Vec<String>
}

impl State {
    fn new() -> State {
        State{text: String::from(""), predicate_names: Vec::new()}
    }

    fn predicate(&mut self, name: &str) -> String {
        let mut result = String::from(name);
        let mut suffix = 0;
        while self.has_predicate(&result){
            suffix += 1;
            result = format!("{name}_{suffix}");
        }
        self.predicate_names.push(result.clone());
        result
    }

    fn has_predicate(&self, name: &String) -> bool{
        self.predicate_names.contains(name)
    }

    fn add(&mut self, line: String){
        self.text.push_str(&line)
    }
    fn add_line(&mut self, line: String){
        self.add(line);
        self.text.push_str(" .\n");
    }
    fn add_rule(&mut self, head: &dyn Solution, body: Vec<&dyn Solution>){
        let head_str = format_solution(head);
        let body_strings: Vec<String> = body.iter().map(|s| format_solution(*s)).collect();
        let body_str = body_strings.join(", ");
        self.add_line(format!("{head_str} :- {body_str}"));
    }
}


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
    let solution_str = format_solution(&solution);
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
    let variables = combine_variables(&left_solution, &right_solution);
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

fn translate(query_str: &str) -> Result<String, TranslateError> {
    let mut state = State::new();
    let query = Query::parse(query_str, None)?;
    let solution = translate_query(&mut state, &query)?;
    state.add("@output ".to_string());
    state.add(solution.pred().clone());
    state.add(" .".to_string());
    Ok(state.text)
}

fn _test_parsing() {
    let query_str = "
        prefix s: <https://xxx#>

        SELECT ?s
        WHERE {
            ?s <https://p> s:a .
            ?s ?p ?o .
            ?s s:p* | a s:o ; s:p s:o2 .
            FILTER NOT EXISTS {
                { ?s ?p3 ?p4 .}
                UNION
                { ?s ?p3 ?p5 . }
            }
            FILTER(?s > 8)
        }
        ORDER BY ?s
    ";
    let query = Query::parse(query_str, None).unwrap();

    println!("Hello, world!");
    println!("{}", query.to_string());
    println!("{}", query.to_sse());

    println!("{:#?}", match &query {
        Query::Select { pattern: GraphPattern::Project {inner, .. }, .. } => inner,
        _ => panic!("Unexpected pattern")
    });
    println!("{:#?}", query);
}


fn _my_to_string(s: &String) -> String{
    s.to_string()
}

fn _test_rust(){
    println!("testing rust...");
    let s = String::from("abc");
    let tmp = _my_to_string(&s);
    let b = tmp.as_str();
    println!("{}", b);
}


fn _test_translation(){
    let _query_str = "
        prefix ex: <https://example.com/>

        SELECT ?object
        WHERE {
            ?subject ex:p ?object .
            ?subject ex:p ex:o .
        }
    ";

    let query_str = "
    PREFIX book: <http://example.org/book/>
PREFIX author: <http://example.org/author/>

SELECT ?title
WHERE {
  ?book book:hasTitle ?title .
  ?book book:writtenBy ?author .

  # Subquery to find authors who have written a Science Fiction book
  {
    SELECT ?author
    WHERE {
      ?sciFiBook book:writtenBy ?author .
      ?sciFiBook book:hasGenre \"Science Fiction\" .
    }
  }
}

    ";
    println!("translating query:");
    println!("{}", query_str);
    let result = translate(query_str);
    println!();
    println!("result:");
    match result{
        Err(error) => println!("{:#?}", error),
        Ok(nemo_string) => println!("{}", nemo_string),
    }
}


fn main() {
    _test_translation();
}
