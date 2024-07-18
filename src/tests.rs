use std::collections::HashSet;
use nemo::datavalues::AnyDataValue;
use nemo::error::Error;
use nemo::execution::{DefaultExecutionEngine, ExecutionEngine};
use nemo::io::ImportManager;
use nemo::io::parser::parse_program;
use nemo::io::resource_providers::ResourceProviders;
use crate::translation_next::translate;

fn execute_nemo(program_string: String) -> Result<Vec<Vec<AnyDataValue>>, Error> {
    println!("{}", program_string);
    let program = parse_program(program_string)?;
    let import_manager = ImportManager::new(ResourceProviders::from(vec![]));
    let mut engine: DefaultExecutionEngine = ExecutionEngine::initialize(&program, import_manager)?;
    engine.execute()?;
    let mut output_iterator = program.output_predicates();
    let output_predicate = output_iterator.next().expect("program has no output");
    assert_eq!(output_iterator.next(), None, "program has more than one output");
    let result = match engine.predicate_rows(output_predicate)? {
        Some(output) => output.collect(),
        None => vec![]
    };
    Ok(result)
}

fn parse_expectation(expectation: &str) -> Vec<Vec<String>> {
    expectation
        .split(|c| c == ';' || c == '\n')
        .map(|row| row.split(',').map(|s| s.trim().to_string()).collect())
        .filter(|row: &Vec<String>| row != &vec!["".to_string()])
        .collect()
}

fn any_data_values_to_string(vec: Vec<Vec<AnyDataValue>>) -> HashSet<Vec<String>> {
    vec.into_iter()
        .map(|row| row.iter().map(|a| a.to_string()).collect())
        .collect()
}

fn compare_vecs(vec: Vec<Vec<AnyDataValue>>, expectation: &str) -> Result<(), String> {
    let expected_set: HashSet<Vec<String>> = parse_expectation(expectation).into_iter().collect();
    let actual_set: HashSet<Vec<String>> = any_data_values_to_string(vec);

    let missing: Vec<Vec<String>> = expected_set.difference(&actual_set).cloned().collect();
    let extra: Vec<Vec<String>> = actual_set.difference(&expected_set).cloned().collect();

    if !missing.is_empty() || !extra.is_empty() {
        let mut error_message = String::new();

        if !missing.is_empty() {
            error_message.push_str(
                &format!(
                    "Missing rows:\n{}\n",
                    missing
                        .into_iter()
                        .map(|row| row.join(", "))
                        .collect::<Vec<_>>()
                        .join("\n")
                )
            );
        }

        if !extra.is_empty() {
            error_message.push_str(
                &format!(
                    "Extra rows:\n{}\n",
                    extra
                        .into_iter()
                        .map(|row| row.join(", "))
                        .collect::<Vec<_>>()
                        .join("\n")
                )
            );
        }

        return Err(error_message);
    }

    Ok(())
}

fn assert_nemo(program: String, inputs: &str, expectation: &str) -> Result<(), Error> {
    let result = execute_nemo(format!("{}\n{}", inputs, program))?;
    match compare_vecs(result, expectation) {
        Ok(()) => Ok(()),
        Err(message) => panic!("{}", message),
    }
}

fn assert_sparql(sparql: &str, inputs: &str, expectation: &str) -> Result<(), Error> {
    let translation_result = translate(sparql);
    let nemo_program = match translation_result {
        Ok(program) => program,
        Err(translation_error) => panic!("{:#?}", translation_error),
    };
    assert_nemo(nemo_program, inputs, expectation)
}


#[test]
fn testing_works() {
    assert_eq!(1+1, 2);
}

#[test]
fn nemo_working() -> Result<(), Error>{
    assert_nemo(
        "p(1, 2) .\n@output p .".to_string(),
        "p(3, 5) .",
        "1, 2; 3, 5"
    )
}

#[test]
fn bgp_simple() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b ?c
            WHERE
            {
              ?a ?b ?c .
            }
        ",
        "
            input_graph(1, 2, 3) .
            input_graph(2, 4, 5) .
         ",
        "
            1, 2, 3
            2, 4, 5
        "
    )
}

#[test]
fn bgp() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?c
            WHERE
            {
              ?a ex:p ?c .
              ?a ex:q ?c .
              ?c ex:p ex:o .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 3) .
            input_graph(1, ex:q, 3) .
            input_graph(3, ex:p, ex:o) .
            input_graph(1, ex:p, 4) .
            input_graph(1, ex:q, 4) .
            input_graph(4, ex:p, ex:o) .
            input_graph(1, ex:p, 5) .
            input_graph(1, ex:q, 5) .
         ",
        "
            1, 3
            1, 4
        "
    )
}

#[test]
fn filter() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?b .
                FILTER(?b)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
            input_graph(2, ex:p, 1) .
         ",
        "2"
    )
}

#[test]
fn filter_without_effective_boolean_value() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?b .
                FILTER(true)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
            input_graph(2, ex:p, 1) .
         ",
        "1; 2"
    )
}


#[test]
fn or() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?x .
                ?a ex:q ?y .
                FILTER(?x || ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
            input_graph(1, ex:q, 0) .
            input_graph(2, ex:p, 1) .
            input_graph(2, ex:q, 0) .
            input_graph(3, ex:p, 0) .
            input_graph(3, ex:q, 1) .
            input_graph(4, ex:p, 1) .
            input_graph(4, ex:q, 1) .
         ",
        "2; 3; 4"
    )
}

#[test]
fn and() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?x .
                ?a ex:q ?y .
                FILTER(?x && ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
            input_graph(1, ex:q, 0) .
            input_graph(2, ex:p, 1) .
            input_graph(2, ex:q, 0) .
            input_graph(3, ex:p, 0) .
            input_graph(3, ex:q, 1) .
            input_graph(4, ex:p, 1) .
            input_graph(4, ex:q, 1) .
         ",
        "4"
    )
}

#[test]
fn not() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?x .
                ?a ex:q ?y .
                FILTER(?x && !?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
            input_graph(1, ex:q, 0) .
            input_graph(2, ex:p, 1) .
            input_graph(2, ex:q, 0) .
            input_graph(3, ex:p, 0) .
            input_graph(3, ex:q, 1) .
            input_graph(4, ex:p, 1) .
            input_graph(4, ex:q, 1) .
         ",
        "2"
    )
}

#[test]
fn same_term() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?x .
                ?a ex:q ?y .
                FILTER(sameTerm(?x, ?y))
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, \"a\") .
            input_graph(1, ex:q, \"a\"@en) .
            input_graph(2, ex:p, \"a\") .
            input_graph(2, ex:q, \"a\") .
         ",
        "2"
    )
}

#[test]
fn comparisons() -> Result<(), Error> {
    let t = "\"true\"^^<http://www.w3.org/2001/XMLSchema#boolean>";
    let f = "\"false\"^^<http://www.w3.org/2001/XMLSchema#boolean>";
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?g ?ge ?s ?se ?e ?ne
            WHERE
            {
                ?a ex:p ?x .
                ?a ex:q ?y .
                BIND(?x > ?y as ?g)
                BIND(?x >= ?y as ?ge)
                BIND(?x < ?y as ?s)
                BIND(?x <= ?y as ?se)
                BIND(?x = ?y as ?e)
                BIND(?x != ?y as ?ne)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
            input_graph(1, ex:q, 1) .
            input_graph(2, ex:p, 1) .
            input_graph(2, ex:q, 1) .
            input_graph(3, ex:p, 2) .
            input_graph(3, ex:q, 1) .
         ",
        &vec![
            vec!["1", f, f, t, t, f, t].join(", "),
            vec!["2", f, t, f, t, t, f].join(", "),
            vec!["3", t, t, f, f, f, t].join(", "),
        ].join("; ")
    )
}

#[test]
fn operators() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?pos ?a ?s ?m ?d ?ua ?us
            WHERE
            {
                ?pos ex:p ?x .
                ?pos ex:q ?y .
                BIND(?x + ?y as ?a)
                BIND(?x - ?y as ?s)
                BIND(?x * ?y as ?m)
                BIND(?x / ?y as ?d)
                BIND(+?x as ?ua)
                BIND(-?x as ?us)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
            input_graph(1, ex:q, 1) .
            input_graph(2, ex:p, 1) .
            input_graph(2, ex:q, 1) .
            input_graph(3, ex:p, 2) .
            input_graph(3, ex:q, 1) .
            input_graph(4, ex:p, 4) .
            input_graph(4, ex:q, 2) .
        ",
        "
            1, 1, -1, 0, 0, 0,  0
            2, 2,  0, 1, 1, 1, -1
            3, 3,  1, 2, 2, 2, -2
            4, 6,  2, 8, 2, 4, -4
        "
    )
}

#[test]
fn in_expression() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?x .
                FILTER(?x in (5, 7))
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 5) .
            input_graph(2, ex:p, 6) .
            input_graph(3, ex:p, 7) .
         ",
        "1; 3"
    )
}


#[test]
fn exists() -> Result<(), Error> {
    let sparql = "
        prefix ex: <https://example.com/>

        SELECT DISTINCT ?x
        WHERE
        {
            ?a ex:p ?x .
            FILTER EXISTS {?x ex:q ex:o1 .}
        }
    ";
    assert_sparql(
        sparql,
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 2) .
            input_graph(1, ex:p, 3) .
            input_graph(2, ex:q, ex:o2) .
            input_graph(3, ex:q, ex:o1) .
         ",
        "3"
    )?;
    assert!(!translate(sparql).expect("translation error").contains("~"), "positive filter should not contain negation");
    Ok(())
}

#[test]
fn not_exists() -> Result<(), Error> {
    let sparql = "
        prefix ex: <https://example.com/>

        SELECT DISTINCT ?x
        WHERE
        {
            ?a ex:p ?x .
            FILTER NOT EXISTS {?x ex:q ex:o1 .}
        }
    ";
    assert_sparql(
        sparql,
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 2) .
            input_graph(1, ex:p, 3) .
            input_graph(2, ex:q, ex:o2) .
            input_graph(3, ex:q, ex:o1) .
         ",
        "2"
    )?;
    assert!(translate(sparql).expect("translation error").contains("~"), "negative filter should contain negation using '~', exists test expects this");
    Ok(())
}

#[test]
fn if_expression() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?x ?y
            WHERE
            {
                ?a ex:p ?x .
                BIND(IF(?x, \"yay\", ?a) as ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
            input_graph(2, ex:p, 3) .
         ",
        "0, 1; 3, \"yay\""
    )
}

#[test]
fn bind() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?y
            WHERE
            {
                ?a ex:p ?x .
                BIND(?x as ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 5) .
            input_graph(2, ex:p, 6) .
         ",
        "1, 5; 2, 6"
    )
}

#[test]
fn bind_with_expression_error() -> Result<(), Error> {
    // this is not correct sparql behaviour yet
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?y
            WHERE
            {
                ?a ex:p ?x .
                BIND(+?x as ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 5) .
            input_graph(2, ex:p, ex:nan) .
         ",
        "1, 5; 2, _:0"
    )
}
