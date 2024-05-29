use crate::solutions;
use crate::solutions::Solution;

#[derive(Debug)]
pub struct State {
    text: String,
    predicate_names: Vec<String>
}

impl State {
    pub fn new() -> State {
        State{text: String::from(""), predicate_names: Vec::new()}
    }

    pub fn predicate(&mut self, name: &str) -> String {
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

    pub fn add(&mut self, line: String){
        self.text.push_str(&line)
    }
    pub fn add_line(&mut self, line: String){
        self.add(line);
        self.text.push_str(" .\n");
    }
    pub fn add_rule(&mut self, head: &dyn Solution, body: Vec<&dyn Solution>){
        let head_str = solutions::format_solution(head);
        let body_strings: Vec<String> = body.iter().map(|s| solutions::format_solution(*s)).collect();
        let body_str = body_strings.join(", ");
        self.add_line(format!("{head_str} :- {body_str}"));
    }

    pub fn to_string(self) -> String{
        self.text
    }
}
