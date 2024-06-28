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
use nemo_model::{nemo_declare, nemo_add, nemo_def, nemo_predicate_type, nemo_var, nemo_call, nemo_iri, nemo_filter};
use nemo_model::TypedPredicate;
use crate::nemo_model::{Basic, construct_program};

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

macro_rules! call_method {
    ($obj:expr, $method:ident) => {{$obj}.$method()};
}

const POSITIONS: [&str; 1+{stringify!(a).len()}+1] = ["abc", "xyz", "ooo"];

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

    println!("{}", call_method!("xyu", to_uppercase));
    println!("{}", POSITIONS.iter().position(|s| *s == "xyz").unwrap())
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


nemo_predicate_type!(PTF = f1 f2 ... f3 f4);
nemo_predicate_type!(PTF2 = f1 f2 ... f3 f4);

fn _test_model(){
    let a = nemo_model::Variable::create("a");
    let b = nemo_model::Variable::create("b");
    let x = "abc".to_string();
    nemo_declare!(p(a, b));
    nemo_add!(p(x, true) .);
    nemo_add!(p(x, false) .);

    let x = {
        nemo_def!(a(??x) :- p(?opy, ??x); Basic);
        a
    };
    let y = x.clone();
    nemo_def!(a(?a, ?b) :- p(?a, ?b); Basic);
    nemo_def!(b(??a, ??x) :- a(??a, ??x), x(??x), y(??x); Basic);
    nemo_add!(b(?a, ?b) :- p(?b, ?a), a(?a, ?b));
    let ex = "https://example.org/";
    nemo_add!(a(nemo_iri!(a), nemo_iri!(ex => b)) .);

    print!("{}", construct_program(&b));
    //println!("{:#?}", b);

    nemo_def!(f(@f1: ?a, @f2: ?b; ?b, ??inner, ?a; @f3: ?a, @f4: ?a) :- p(??inner), p(?a, ?b); PTF);
    print!("{}", construct_program(&f));

    let v1 = nemo_var!(v1);
    let v2 = nemo_model::Variable::create("2");
    let rr = nemo_var!(!rr);
    nemo_def!(g(v1, "abc", 7, true, 4.4, rr, rr, nemo_var!(!rr), nemo_call!(DO_IT; v1, 1) + 2 + 3, nemo_iri!(gg)) :- p(v2, v1); Basic);
    print!("{}", construct_program(&g));

    nemo_def!(h(%count(??vars)) :- p(??vars); Basic);
    print!("{}", construct_program(&h));

    nemo_def!(i(?x, ?b) :- p(?x, ?b), {&p}, {nemo_filter!("", ?x, " < ", 1, "")}; Basic);
    print!("{}", construct_program(&i));
}


fn main() {
    _test_model();
}
