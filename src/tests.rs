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
fn path_alternative() -> Result<(), Error> {
    /// also tests named node and reverse
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a ex:p|^ex:q ?b .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 100) .
            input_graph(2, ex:x, 200) .
            input_graph(3, ex:q, 300) .
         ",
        "1, 100; 300, 3"
    )
}

#[test]
fn path_one_or_more() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a ex:p+ ?b .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
            input_graph(222, ex:p, 2222) .
         ",
        "1, 11; 2, 22; 2, 222; 2, 2222; 22, 222; 22, 2222; 222, 2222"
    )
}

#[test]
fn path_zero_or_more() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a ex:p* ?b .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "1, 11; 2, 22; 2, 222; 22, 222; 1, 1; 2, 2; 22, 22; 222, 222; 11, 11"
    )
}

#[test]
fn path_zero_or_one() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a ex:p? ?b .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "1, 11; 2, 22; 22, 222; 1, 1; 2, 2; 22, 22; 222, 222; 11, 11"
    )
}

#[test]
fn path_constants() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p* 222 .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "2; 22; 222"
    )?;
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                2 ex:p* ?a .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "2; 22; 222"
    )?;
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix xsd: <http://www.w3.org/2001/XMLSchema#>

            SELECT DISTINCT ?a
            WHERE
            {
                2 ex:p* \"2\"^^xsd:integer .
                BIND(42 as ?a)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "42"
    )?;
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix xsd: <http://www.w3.org/2001/XMLSchema#>

            SELECT DISTINCT ?a
            WHERE
            {
                2 ex:q* 2 .
                BIND(42 as ?a)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "42"
    )?;
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix xsd: <http://www.w3.org/2001/XMLSchema#>

            SELECT DISTINCT ?a
            WHERE
            {
                2 ex:q* 1 .
                BIND(42 as ?a)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        ""
    )?;
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix xsd: <http://www.w3.org/2001/XMLSchema#>

            SELECT DISTINCT ?a
            WHERE
            {
                5 ex:q* 5 .
                BIND(42 as ?a)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "42"
    )?;  // is this standard behaviour? 5 is neither subject nor object so is there really a zero length path between it?
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix xsd: <http://www.w3.org/2001/XMLSchema#>

            SELECT DISTINCT ?a
            WHERE
            {
                5 ex:q* ?a .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "5"
    )?;  // is this standard behaviour? same as above?
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix xsd: <http://www.w3.org/2001/XMLSchema#>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:q* 5 .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "5"
    )?;  // is this standard behaviour? same as above?
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix xsd: <http://www.w3.org/2001/XMLSchema#>

            SELECT DISTINCT ?a
            WHERE
            {
                1 ex:q* ?a .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:p, 22) .
            input_graph(22, ex:p, 222) .
         ",
        "1"
    )?;
    Ok(())
}

#[test]
fn path_negated_property_set() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a !(ex:q|ex:p) ?b .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:q, 22) .
            input_graph(3, ex:x, 33) .
         ",
        "3, 33"
    )
}

#[test]
fn path_inverse_negated_property_set() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a !(ex:p|^ex:p) ?b .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:q, 22) .
            input_graph(3, ex:x, 33) .
         ",
        "2, 22; 3, 33; 22, 2; 33, 3"
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
fn int_functions() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix math: <http://www.w3.org/2005/xpath-functions/math#>
            prefix fn: <https://www.w3.org/2005/xpath-functions#>

            SELECT DISTINCT ?x ?str ?datatype ?abs ?sqrt ?pow ?sum ?min ?max
            WHERE
            {
                ?a ex:p ?x .
                BIND(str(?x) as ?str)
                BIND(datatype(?x) as ?datatype)
                BIND(ABS(?x) as ?abs)
                BIND(math:sqrt(if(?x > 0, ?x, 16)) as ?sqrt)
                BIND(math:pow(?x, 3) as ?pow)
                BIND(fn:sum(?x, ?x, 7) as ?sum)
                BIND(fn:min(?x, 2, 0) as ?min)
                BIND(fn:max(?x, 3, 0) as ?max)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, -2) .
            input_graph(2, ex:p, 4) .
         ",
        "
            -2, \"-2\", <http://www.w3.org/2001/XMLSchema#int>, 2, 4, -8, 3, -2, 3
             4, \"4\", <http://www.w3.org/2001/XMLSchema#int>, 4, 2, 64, 15, 0, 4
        "
    )
}

#[test]
fn float_functions() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix math: <http://www.w3.org/2005/xpath-functions/math#>

            SELECT DISTINCT ?x ?str ?datatype ?ceil ?floor ?sin ?cos ?tan
            WHERE
            {
                ?a ex:p ?x .
                BIND(str(?x) as ?str)
                BIND(datatype(?x) as ?datatype)
                BIND(ceil(?x) as ?ceil)
                BIND(floor(?x) as ?floor)
                BIND(math:sin(?x) as ?sin)
                BIND(math:cos(?x) as ?cos)
                BIND(math:tan(?x) as ?tan)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, -2.4) .
            input_graph(2, ex:p, 3.6) .
         ",
        vec![
            vec![
                "\"-2.4\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"-2.4\"",
                "<http://www.w3.org/2001/XMLSchema#double>",
                "\"-2\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"-3\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"-0.675463180551151\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"-0.7373937155412454\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"0.9160142896734107\"^^<http://www.w3.org/2001/XMLSchema#double>",
            ].join(","),
            vec![
                "\"3.6\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"3.6\"",
                "<http://www.w3.org/2001/XMLSchema#double>",
                "\"4\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"3\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"-0.44252044329485246\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"-0.896758416334147\"^^<http://www.w3.org/2001/XMLSchema#double>",
                "\"0.4934667299849038\"^^<http://www.w3.org/2001/XMLSchema#double>",
            ].join(","),
        ].join(";").as_str()
    )
}

#[test]
fn round() -> Result<(), Error> {
    // this tests things that are not standard compliant
    assert_sparql(
        "
            prefix ex: <https://example.com/>
            prefix math: <http://www.w3.org/2005/xpath-functions/math#>

            SELECT DISTINCT ?a ?y
            WHERE
            {
                ?a ex:p ?x .
                BIND(round(?x) as ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 2.4999) .
            input_graph(2, ex:p, 2.5001) .
            input_graph(3, ex:p, 2.5) .
            input_graph(4, ex:p, -2.5) .
            input_graph(5, ex:p, \"a\") .
         ",
        &vec![
            "1, \"2\"^^<http://www.w3.org/2001/XMLSchema#double>",
            "2, \"3\"^^<http://www.w3.org/2001/XMLSchema#double>",
            "3, \"3\"^^<http://www.w3.org/2001/XMLSchema#double>",
            "4, \"-3\"^^<http://www.w3.org/2001/XMLSchema#double>",  // standard would be -2
            "5, _:0"  // this needs to change when handling undefined values better
        ].join("\n"),
    )
}

#[test]
fn str_functions() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?x ?str ?datatype ?concat ?substr1 ?substr2 ?len ?u ?l ?before ?before_empty ?after ?after_empty
            WHERE
            {
                ?a ex:p ?x .
                BIND(str(?x) as ?str)
                BIND(datatype(?x) as ?datatype)
                BIND(concat(?x, \"abc\") as ?concat)
                BIND(substr(?x, 2) as ?substr1)
                BIND(substr(?x, 2, 3) as ?substr2)
                BIND(strlen(?x) as ?len)
                BIND(ucase(?x) as ?u)
                BIND(lcase(?x) as ?l)
                BIND(strbefore(?x, \"ab\") as ?before)
                BIND(strbefore(?x, \"\") as ?before_empty)
                BIND(strafter(?x, \"ab\") as ?after)
                BIND(strafter(?x, \"\") as ?after_empty)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, \"\") .
            input_graph(2, ex:p, \"A\") .
            input_graph(3, ex:p, \"abcd\"^^<http://www.w3.org/2001/XMLSchema#string>) .
            input_graph(4, ex:p, \"cdab\") .
            input_graph(5, ex:p, \"1234🧑‍💻\") .
         ", // note that the part after 1234 (however it may be represented by your text renderer) is the tree-part unicode symbol for technologist
        "
            \"\",    \"\",      <http://www.w3.org/2001/XMLSchema#string>, \"abc\",    \"\",      \"\",    0, \"\",     \"\",     \"\",  \"\", \"\",  \"\"
            \"A\",   \"A\",     <http://www.w3.org/2001/XMLSchema#string>, \"Aabc\",   \"\",      \"\",    1, \"A\",    \"a\",    \"\",  \"\", \"\",  \"A\"
            \"abcd\", \"abcd\", <http://www.w3.org/2001/XMLSchema#string>, \"abcdabc\",\"bcd\",   \"bcd\", 4, \"ABCD\", \"abcd\", \"\",  \"\", \"cd\",\"abcd\"
            \"cdab\", \"cdab\", <http://www.w3.org/2001/XMLSchema#string>, \"cdababc\",\"dab\",   \"dab\", 4, \"CDAB\", \"cdab\", \"cd\",\"\", \"\",  \"cdab\"
            \"1234🧑‍💻\",\"1234🧑‍💻\",<http://www.w3.org/2001/XMLSchema#string>, \"1234🧑‍💻abc\",\"234🧑‍💻\", \"234\", 5, \"1234🧑‍💻\",\"1234🧑‍💻\",\"\",  \"\", \"\",  \"1234🧑‍💻\"
        "
    )
}

#[test]
fn lang() -> Result<(), Error> {
    // this tests things that are not standard compliant
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?y
            WHERE
            {
                ?a ex:p ?x .
                BIND(lang(?x) as ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, \"a\") .
            input_graph(2, ex:p, \"a\"@de) .
         ",
        "1, _:0; 2, \"de\""  // should be empty string instead of null by standard
    )
}

#[test]
fn str_bool_functions() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?contains ?starts ?ends
            WHERE
            {
                ?a ex:p ?contains .
                ?a ex:p ?starts .
                ?a ex:p ?ends .
                FILTER(contains(?contains, \"ab\"))
                FILTER(strstarts(?starts, \"ab\"))
                FILTER(strends(?ends, \"ab\"))
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, \"abc\") .
            input_graph(1, ex:p, \"cab\") .
            input_graph(1, ex:p, \"xyz\") .
         ",
        "
            \"abc\", \"abc\", \"cab\"
            \"cab\", \"abc\", \"cab\"
        "
    )
}

#[test]
fn regex() -> Result<(), Error> {
    // this tests for things that are incorrect regarding the standard
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?x .
                ?a ex:q ?y
                FILTER regex(?x, ?y)
                BIND(\"\\\\\" as ?o)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, \"Alice\") .
            input_graph(1, ex:q, \"^Ali\") .
            input_graph(2, ex:p, \"Bob\") .
            input_graph(2, ex:q, \"^Ali\") .
            input_graph(3, ex:p, \"Alice\") .
            input_graph(3, ex:q, \"^Ali$\") .
            input_graph(4, ex:p, \"aaaaa\") .
            input_graph(4, ex:q, \"^a{5}\") .
            input_graph(5, ex:p, \"xabcx\") .
            input_graph(5, ex:q, \"(x|y).*(x|y)\") .
            input_graph(6, ex:p, \"xabcx\") .
            dummy(1) .
            input_graph(6, ex:q, CONCAT(\"(x|y).*\", SUBSTR(\"\\\\1\", 2))) :- dummy(1) .
         ",
        "1; 4; 5"  // standard would also require 6 which is (x|y).*\1
    )
}


#[test]
fn node_type_checks() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?iri ?blank ?literal ?numeric
            WHERE
            {
                ex:s ex:p ?iri .
                ex:s ex:p ?blank .
                ex:s ex:p ?literal .
                ex:s ex:p ?numeric .
                FILTER(isIRI(?iri))
                FILTER(isBlank(?blank))
                FILTER(isLiteral(?literal))
                FILTER(isNumeric(?numeric))
                FILTER(?numeric != ?literal)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            dummy(1) .
            bnode(!bnode) :- dummy(1) .
            input_graph(ex:s, ex:p, ex:o) .
            input_graph(ex:s, ex:p, ?bnode) :- bnode(?bnode) .
            input_graph(ex:s, ex:p, \"a\") .
            input_graph(ex:s, ex:p, 2) .
         ",
        "<https://example.com/o>, _:0, \"a\", 2"
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
