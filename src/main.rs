mod solutions;
mod error;
mod state;
mod translation;

use spargebra::algebra::GraphPattern;
use spargebra::Query;

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

fn _test_rust(){
    println!("testing rust...");
    let s = String::from("abc");
    let tmp = _my_to_string(&s);
    let b = tmp.as_str();
    println!("{}", b);
}


fn _test_translation(){
    let query_str = "
        prefix ex: <https://example.com/>

        SELECT DISTINCT *
        WHERE {
            ?subject ^(ex:p1) ?object .
        }
    ";

    let _query_str = "
    PREFIX book: <http://example.org/book/>
PREFIX author: <http://example.org/author/>

SELECT DISTINCT ?title
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
    _test_translation();
}
