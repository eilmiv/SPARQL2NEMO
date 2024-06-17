mod basic_solutions;
mod error;
mod state;
mod translation;
mod solution;

use std::rc::Rc;
use spargebra::algebra::GraphPattern;
use spargebra::Query;
use crate::solution::{Column};

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
        order by ?c DESC(?a)

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


fn main() {
    _test_translation();
}
