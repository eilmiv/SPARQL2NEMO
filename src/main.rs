mod basic_solutions;
mod error;
mod state;
mod translation;
mod solution;
mod nemo_model;

use std::rc::Rc;
use spargebra::algebra::GraphPattern;
use spargebra::Query;
use crate::solution::{Column};
use nemo_model::{nemo_declare, nemo_add, nemo_def};
use nemo_model::TypedPredicate;
use crate::nemo_model::{Basic, construct_program, GenState};

fn _test_parsing() {
    let query_str = "
        prefix s: <https://xxx#>

        SELECT DISTINCT (?s + 1 AS ?x)
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

    println!("{:#?}", query);

    println!("{:#?}", match &query {
        Query::Select { pattern: GraphPattern::Project {inner, .. }, .. } => inner,
        _ => panic!("Unexpected pattern")
    });
}


fn _my_to_string(s: &String) -> String{
    s.to_string()
}

macro_rules! my_vec {
    //($($elem:expr),*) => {vec![$($elem, $elem),*]};
    //($($elem:expr)=>*) => {vec![$($elem),*]};
    //%($($elem:expr)*) => {vec![$($elem),*]};
    //%($last:expr => $($elem:expr),*) => {vec![$($elem),*, $last]};
    ($head:literal :- $($body:literal),+ .) => {vec![$head, $($body),+]};
    ($head:literal .) => {vec![$head]};
    (abc) => {vec![55]};
    ($($first:literal),+ . $($second:literal and $($third:literal),+);+) => {vec![$($first),+, $($second, $($third),+),+]};
}

fn _test_rust(){
    println!("testing rust...");
    let s = String::from("abc");
    let tmp = _my_to_string(&s);
    let _b = tmp.as_str();
    let _i = 3;
    println!("{:?}", my_vec!(
        1, 2, 3 .
        4 and 0; 5 and -1
    ));
    let v1= Rc::new(Column::new("abc"));
    let v2= v1.clone();
    println!("equal: {}", Rc::ptr_eq(&v1, &v2));
    let v3: Rc<Column> = v2.into();
    println!("{:?}", v3);
}


fn _test_translation(){
    let query_str = "
        prefix ex: <https://example.com/>

        SELECT ?a ?b ?c
        WHERE
        {
          ?a ?b ?c .
        }
        order by (?a + ?b)

    ";

    println!("translating query:");
    println!("{}", query_str);
    let result = translation::translate(query_str);
    println!();
    println!("result:");
    match result{
        Err(error) => println!("{:#?}", error),
        Ok(nemo_string) => println!("{}", nemo_string),
    }
}

fn _test_model(){
    let a = nemo_model::Variable::create("a");
    let b = nemo_model::Variable::create("b");
    let x = "abc".to_string();
    nemo_declare!(p(a, b));
    nemo_add!(p(&x, "true") .);
    nemo_add!(p(x, "false") .);

    nemo_def!(a(?a, ?b) :- p(?a, ?b); Basic);
    nemo_def!(b(?a, ?b) :- a(?a, ?b); Basic);
    nemo_add!(b(?a, ?b) :- p(?b, ?a));

    print!("{}", construct_program(&b));
    //println!("{:#?}", b);
}


fn main() {
    _test_model();
}
