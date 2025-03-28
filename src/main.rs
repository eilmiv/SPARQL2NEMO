mod error;
mod solution;
mod nemo_model;
mod translation;

#[cfg(test)]
mod tests;

use std::io;
use std::io::Read;
use std::rc::Rc;
use spargebra::algebra::GraphPattern;
use spargebra::Query;
use crate::solution::{Column};
use nemo_model::{nemo_declare, nemo_add, nemo_def, nemo_predicate_type, nemo_var, nemo_call, nemo_iri, nemo_filter};
use nemo_model::TypedPredicate;
use crate::nemo_model::{Basic, construct_program};

fn _test_parsing() {
    let query_str = "
        prefix ex: <https://example.com/>

        SELECT DISTINCT (SUM(DISTINCT ?a) as ?s)
        WHERE {
            ?a ex:p ?b .
        }
    ";
    let query = Query::parse(query_str, None).unwrap();

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

const _POSITIONS: [&str; 1+{stringify!(a).len()}+1] = ["abc", "xyz", "ooo"];

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
    println!("{}", _POSITIONS.iter().position(|s| *s == "xyz").unwrap())
}


fn _test_translation(){
    let query_str = "
        prefix ex: <https://example.com/>

        SELECT DISTINCT ?a {
            ?a ex:p ex:o .
            FILTER NOT EXISTS {
                ?a ex:q ex:o .
            }
        }
    ";

    let query_str = "
        prefix ex: <https://example.com/>
        prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#rest>

        SELECT DISTINCT ?x (SUM(coalesce(?a, 1, 3)) as ?s) {
            ?x ex:p ?a
        }
        GROUP BY ?x
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

fn _translate_stdin(){
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("STDIN read error");
    let query_str = input.as_str();

    let result = translation::translate(query_str).expect("Translation error");
    println!("{}", result);
}


nemo_predicate_type!(PTF = f1 f2 ... f3 f4);
nemo_predicate_type!(PTF2 = f1 f2 ... f3 f4);

nemo_predicate_type!(MyABCType = a b ... c);

fn _test_model(){
    let a = nemo_model::Variable::create("a");
    /*let b = nemo_model::Variable::create("b");
    let x = "abc".to_string();
    nemo_declare!(p(a, b));
    nemo_add!(p(x, true));
    nemo_add!(p(x, false));

    let x = {
        nemo_def!(a(??x) :- p(?opy, ??x); Basic);
        a
    };
    let y = x.clone();
    nemo_def!(a(?a, ?b) :- p(?a, ?b); Basic);
    nemo_def!(b(??a, ??x) :- a(??a, ??x), x(??x), y(??x); Basic);
    nemo_add!(b(?a, ?b) :- p(?b, ?a), a(?a, ?b));
    let ex = "https://example.org/";
    nemo_add!(a(nemo_iri!(a), nemo_iri!(ex => b)));

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

    nemo_def!(i(?x, ?b) :- ~p(?x, ?b), ~{&p}, {nemo_filter!("", ?x, " < ", 1, "")}; Basic);
    print!("{}", construct_program(&i));*/
    
    nemo_declare!(existing_predicate(a));
    // Rule Start
    nemo_def!(new_predicate(?x) :- existing_predicate(?x); Basic);
    // Rule end
    print!("{}", construct_program(&new_predicate));
}


fn main() {
    _translate_stdin();
}
