mod solutions;
mod error;
mod state;
mod translation;

use spargebra::algebra::GraphPattern;
use spargebra::Query;
use solutions::Solution;

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
    let result = translation::translate(query_str);
    println!();
    println!("result:");
    match result{
        Err(error) => println!("{:#?}", error),
        Ok(nemo_string) => println!("{}", nemo_string),
    }
}


fn main() {
    _test_parsing();
}
