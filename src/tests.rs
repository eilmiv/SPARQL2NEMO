use std::collections::{HashMap, HashSet};
use nemo::datavalues::AnyDataValue;
use nemo::error::Error;
use nemo::execution::{DefaultExecutionEngine, ExecutionEngine};
use nemo::io::ImportManager;
use nemo::io::parser::parse_program;
use nemo::io::resource_providers::ResourceProviders;
use crate::translation::translate;

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
    if expectation.starts_with("[") && expectation.ends_with("]") {
        let inner_expectation = parse_expectation(&expectation[1..expectation.len()-1]);
        return inner_expectation.iter().enumerate().map(|(i, vec)| {
            let mut new_vec = vec.clone();
            new_vec.insert(0, i.to_string());
            new_vec
        }).collect()
    }
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

fn strip_index(row: &Vec<String>) -> Vec<String> {
    row.iter().skip(1).cloned().collect()
}

fn build_frequency_map(set: &HashSet<Vec<String>>, strip: bool) -> HashMap<Vec<String>, usize> {
    let mut map = HashMap::new();
    for row in set {
        let key = if strip { strip_index(row) } else { row.clone() };
        *map.entry(key).or_insert(0) += 1;
    }
    map
}

fn compare_sets(
    expected_set: &HashSet<Vec<String>>,
    actual_set: &HashSet<Vec<String>>,
    strip: bool
) -> Result<(), String> {
    let expected_map = build_frequency_map(expected_set, strip);
    let actual_map = build_frequency_map(actual_set, strip);

    let mut extra_rows = vec![];
    let mut missing_rows = vec![];

    // Find missing rows in the actual_set
    for (row, expected_count) in &expected_map {
        let actual_count = actual_map.get(row).unwrap_or(&0);
        if actual_count < expected_count {
            for _ in 0..(expected_count - actual_count) {
                missing_rows.push(row.clone());
            }
        }
    }

    // Find extra rows in the actual_set
    for (row, actual_count) in &actual_map {
        let expected_count = expected_map.get(row).unwrap_or(&0);
        if actual_count > expected_count {
            for _ in 0..(actual_count - expected_count) {
                extra_rows.push(row.clone());
            }
        }
    }

    if !missing_rows.is_empty() || !extra_rows.is_empty() {
        let mut error_message = String::new();

        if !missing_rows.is_empty() {
            error_message.push_str(
                &format!(
                    "Missing rows:\n{}\n",
                    missing_rows
                        .into_iter()
                        .map(|row| row.join(", "))
                        .collect::<Vec<_>>()
                        .join("\n")
                )
            );
        }

        if !extra_rows.is_empty() {
            error_message.push_str(
                &format!(
                    "Extra rows:\n{}\n",
                    extra_rows
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

fn compare_expectations(expect: &str, actual: &str, allow_reorder: bool) -> Result<(), String> {
    let expect_set: HashSet<Vec<String>> = parse_expectation(expect).into_iter().collect();
    let actual_set: HashSet<Vec<String>> = parse_expectation(actual).into_iter().collect();
    compare_sets(&expect_set, &actual_set, allow_reorder)
}

fn assert_nemo(program: String, inputs: &str, expectation: &str, allow_reorder: bool) -> Result<(), Error> {
    let result = execute_nemo(format!("{}\n{}", inputs, program))?;
    let expected_set: HashSet<Vec<String>> = parse_expectation(expectation).into_iter().collect();
    let actual_set: HashSet<Vec<String>> = any_data_values_to_string(result);
    match compare_sets(&expected_set, &actual_set, allow_reorder) {
        Ok(()) => Ok(()),
        Err(message) => panic!("{}", message),
    }
}

fn assert_sparql_impl(sparql: &str, inputs: &str, expectation: &str, allow_reorder: bool) -> Result<(), Error> {
    let translation_result = translate(sparql);
    let nemo_program = match translation_result {
        Ok(program) => program,
        Err(translation_error) => panic!("{:#?}", translation_error),
    };
    assert_nemo(nemo_program, inputs, expectation, allow_reorder)
}

fn assert_sparql(sparql: &str, inputs: &str, expectation: &str) -> Result<(), Error> {
    assert_sparql_impl(sparql, inputs, expectation, false)
}

fn assert_sparql_multi(sparql: &str, inputs: &str, expectation: &str) -> Result<(), Error> {
    assert_sparql_impl(sparql, inputs, expectation, true)
}


#[test]
fn testing_works() {
    assert_eq!(1+1, 2);
}

#[test]
fn test_compare_sets() {
    assert_eq!(compare_expectations("[1, abc; 2, def]", "[1, abc; 2, def]", false), Ok(()));
    assert_eq!(compare_expectations("[1, abc; 2, def; 3, ghi]", "[1, abc; 2, def]", false), Err("Missing rows:\n2, 3, ghi\n".to_string()));
    assert_eq!(compare_expectations("[1, abc; 2, def]", "[1, abc; 2, def; 3, ghi]", false), Err("Extra rows:\n2, 3, ghi\n".to_string()));
    assert_eq!(compare_expectations("[1, abc; 2, def; 3, ghi]", "[1, abc; 2, def; 4, jkl]", false), Err("Missing rows:\n2, 3, ghi\nExtra rows:\n2, 4, jkl\n".to_string()));
    assert_eq!(compare_expectations("[1, abc; 2, def]", "[2, def; 1, abc]", true), Ok(()));
    assert_eq!(compare_expectations("[1, abc; 1, abc]", "[1, abc]", true), Err("Missing rows:\n1, abc\n".to_string()));

    assert_eq!(compare_expectations("1, abc; 2, def", "1, abc; 2, def", false), Ok(()));
    assert_eq!(compare_expectations("1, abc; 2, def; 3, ghi", "1, abc; 2, def", false), Err("Missing rows:\n3, ghi\n".to_string()));
    assert_eq!(compare_expectations("1, abc; 2, def", "1, abc; 2, def; 3, ghi", false), Err("Extra rows:\n3, ghi\n".to_string()));
    assert_eq!(compare_expectations("1, abc; 2, def; 3, ghi", "1, abc; 2, def; 4, jkl", false), Err("Missing rows:\n3, ghi\nExtra rows:\n4, jkl\n".to_string()));
}

#[test]
fn nemo_working() -> Result<(), Error>{
    assert_nemo(
        "p(1, 2) .\n@output p .".to_string(),
        "p(3, 5) .",
        "1, 2; 3, 5",
        false
    )
}


#[test]
fn nemo_not_working() -> Result<(), Error>{
    assert_nemo(
        "out(DATATYPE(?a)) :- in(?a), DOUBLE(?a) >= DOUBLE(\"false\"^^xsd:boolean) .\n@output out .".to_string(),
        "
            @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
            in_1(1) .
            in_2(1.0) .
        ",
        "",
        false
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
fn bgp_multi() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a
            WHERE
            {
              ?a ex:p [ex:q ex:o] .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, ex:11) .
            input_graph(ex:11, ex:q, ex:o) .
            input_graph(2, ex:p, ex:20) .
            input_graph(3, ex:p, ex:31) .
            input_graph(ex:31, ex:q, ex:o) .
            input_graph(3, ex:p, ex:32) .
            input_graph(ex:32, ex:q, ex:o) .
            input_graph(3, ex:p, ex:33) .
            input_graph(ex:33, ex:q, ex:o) .
         ",
        "[1; 3; 3; 3]"
    )
}

/// also tests named node and reverse
#[test]
fn path_alternative() -> Result<(), Error> {
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
    )?;  // is this standard behaviour? 5 is neither subject nor object so is there really a zero length path between it? I think this is correct
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
            @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
            dummy(1) .

            input_graph(1, ex:p, 0) .
            input_graph(2, ex:p, 1) .
            input_graph(3, ex:p, 0.0) .
            input_graph(4, ex:p, 1.0) .
            input_graph(5, ex:p, \"true\"^^xsd:boolean) .
            input_graph(6, ex:p, \"false\"^^xsd:boolean) .
            input_graph(7, ex:p, \"abc\") .
            input_graph(8, ex:p, \"\") .
            input_graph(9, ex:p, ex:xyz) .
            input_graph(0, ex:p, !x) :- dummy(1) .
         ",
        "2; 4; 5; 7"
    )
}


#[test]
fn filter_seq() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a
            WHERE
            {
                ?a ex:p ?b .
                FILTER(?b)
            }
        ",
        "
            @prefix ex: <https://example.com/> .
            @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
            dummy(1) .

            input_graph(1, ex:p, 0) .
            input_graph(2, ex:p, 1) .
            input_graph(3, ex:p, 0.0) .
            input_graph(4, ex:p, 1.0) .
            input_graph(5, ex:p, \"true\"^^xsd:boolean) .
            input_graph(6, ex:p, \"false\"^^xsd:boolean) .
            input_graph(7, ex:p, \"abc\") .
            input_graph(8, ex:p, \"\") .
            input_graph(9, ex:p, ex:xyz) .
            input_graph(0, ex:p, !x) :- dummy(1) .
         ",
        "[5; 7; 2; 4]"
    )
}

#[test]
fn filter_multi() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a
            WHERE
            {
                {
                    ?a ex:p ?b .
                    FILTER(?b)
                }
                VALUES (?x) {(0)}
            }
        ",
        "
            @prefix ex: <https://example.com/> .
            @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
            dummy(1) .

            input_graph(1, ex:p, 0) .
            input_graph(2, ex:p, 1) .
            input_graph(3, ex:p, 0.0) .
            input_graph(4, ex:p, 1.0) .
            input_graph(5, ex:p, \"true\"^^xsd:boolean) .
            input_graph(6, ex:p, \"false\"^^xsd:boolean) .
            input_graph(7, ex:p, \"abc\") .
            input_graph(8, ex:p, \"\") .
            input_graph(9, ex:p, ex:xyz) .
            input_graph(0, ex:p, !x) :- dummy(1) .
         ",
        "[5; 7; 2; 4]"
    )
}

#[test]
fn filter_multiplicity() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a
            WHERE
            {
                VALUES (?a) {(ex:error) (0) (1) (2) (2)}
                FILTER(?a)
            }
        ",
        "",
        "[1; 2; 2]"
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
            @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

            input_graph(1, ex:p, 0) .
            input_graph(1, ex:q, 1) .
            input_graph(2, ex:p, 1) .
            input_graph(2, ex:q, 1) .
            input_graph(3, ex:p, 2) .
            input_graph(3, ex:q, 1) .

            input_graph(4, ex:p, 0.1) .
            input_graph(4, ex:q, 1) .
            input_graph(5, ex:p, 1.0) .
            input_graph(5, ex:q, 1) .
            input_graph(6, ex:p, 2.1) .
            input_graph(6, ex:q, 1) .

            input_graph(7, ex:p, \"a\") .
            input_graph(7, ex:q, \"b\") .
            input_graph(8, ex:p, \"aaa\") .
            input_graph(8, ex:q, \"aaa\") .
            input_graph(9, ex:p, \"aaa\") .
            input_graph(9, ex:q, \"a\") .

            input_graph(10, ex:p, \"false\"^^xsd:boolean) .
            input_graph(10, ex:q, \"true\"^^xsd:boolean) .
            input_graph(11, ex:p, \"true\"^^xsd:boolean) .
            input_graph(11, ex:q, \"true\"^^xsd:boolean) .
            input_graph(12, ex:p, \"true\"^^xsd:boolean) .
            input_graph(12, ex:q, \"false\"^^xsd:boolean) .
         ",
        &vec![
            vec!["1", f, f, t, t, f, t].join(", "),
            vec!["2", f, t, f, t, t, f].join(", "),
            vec!["3", t, t, f, f, f, t].join(", "),

            vec!["4", f, f, t, t, f, t].join(", "),
            vec!["5", f, t, f, t, t, f].join(", "),
            vec!["6", t, t, f, f, f, t].join(", "),

            vec!["7", f, f, t, t, f, t].join(", "),
            vec!["8", f, t, f, t, t, f].join(", "),
            vec!["9", t, t, f, f, f, t].join(", "),

            vec!["10", f, f, t, t, f, t].join(", "),
            vec!["11", f, t, f, t, t, f].join(", "),
            vec!["12", t, t, f, f, f, t].join(", "),
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
fn in_with_error() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?x .
                FILTER(?x in (5, STRLEN(4), 1/0.0))
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 5) .
         ",
        "1"
    )
}

#[test]
fn not_in_with_error() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a
            WHERE
            {
                ?a ex:p ?x .
                FILTER(?x not in (3, 1/0))
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 2) .
         ",
        ""
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
fn exists_unbound_pattern() -> Result<(), Error> {
    let sparql = "
        prefix ex: <https://example.com/>

        SELECT DISTINCT ?x
        WHERE
        {
            ?a ex:p ?x .
            FILTER EXISTS {VALUES (?x) {(UNDEF)}}
        }
    ";
    assert_sparql(
        sparql,
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 2) .
            input_graph(1, ex:p, 3) .
         ",
        "2; 3"
    )
}


#[test]
fn exists_unbound_bindings() -> Result<(), Error> {
    let sparql = "
        prefix ex: <https://example.com/>

        SELECT DISTINCT ?x
        WHERE
        {
            VALUES (?x) {(UNDEF) (2)}
            FILTER EXISTS {?a ex:p ?x}
        }
    ";
    assert_sparql(
        sparql,
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 2) .
            input_graph(1, ex:p, 3) .
         ",
        "UNDEF; 2"
    )
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
fn bound() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?x ?y ?err ?x_bound ?un_bound ?never_bound
            WHERE
            {
                ?x ex:p ?y .
                BIND(?x / ?y as ?err)
                BIND(bound(?x) as ?x_bound)
                BIND(bound(?err) as ?un_bound)
                BIND(bound(?never) as ?never_bound)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 0) .
         ",
        "1, 0, UNDEF, \"true\"^^<http://www.w3.org/2001/XMLSchema#boolean>, \"false\"^^<http://www.w3.org/2001/XMLSchema#boolean>, \"false\"^^<http://www.w3.org/2001/XMLSchema#boolean>"
    )
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
fn coalesce() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?t1 ?t2 ?t3 ?t4 ?t5 ?t6
            WHERE
            {
                ?a ex:p ?x .
                BIND(COALESCE(?x, 1/0) as ?t1)
                BIND(COALESCE(1/0, ?x) as ?t2)
                BIND(COALESCE(5, ?x) as ?t3)
                BIND(COALESCE(?y, 3) as ?t4)
                BIND(COALESCE(?y) as ?t5)
                BIND(COALESCE(?y, 1/0, 7, ?x) as ?t6)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 2) .
         ",
        "2, 2, 5, 3, UNDEF, 7"
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
            "5, UNDEF"
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
fn datetime_functions() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?datatype ?year ?month ?day ?hours ?minutes ?seconds
            WHERE
            {
                ?a ex:p ?x .
                BIND(datatype(?x) as ?datatype)
                BIND(year(?x) as ?year)
                BIND(month(?x) as ?month)
                BIND(day(?x) as ?day)
                BIND(hours(?x) as ?hours)
                BIND(minutes(?x) as ?minutes)
                BIND(seconds(?x) as ?seconds)
            }
        ",
        "
            @prefix ex: <https://example.com/> .
            @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

            input_graph(1, ex:p, \"2002-10-11T12:00:00-05:00\"^^xsd:dateTime) .
            input_graph(2, ex:p, \"-2002-11-10T12:00:01.555+05:00\"^^xsd:dateTime) .
            input_graph(3, ex:p, \"002-10-10T12:09:00Z\"^^xsd:dateTime) .
         ",
        "
            1, <http://www.w3.org/2001/XMLSchema#dateTime>, 2002, 10, 11, 12, 0, \"0\"^^<http://www.w3.org/2001/XMLSchema#double>
            2, <http://www.w3.org/2001/XMLSchema#dateTime>, -2002, 11, 10, 12, 0, \"1.555\"^^<http://www.w3.org/2001/XMLSchema#double>
            3, <http://www.w3.org/2001/XMLSchema#dateTime>, 2, 10, 10, 12, 9, \"0\"^^<http://www.w3.org/2001/XMLSchema#double>
        "
    )
}

#[test]
fn datetime_functions_invalid() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?year
            WHERE
            {
                ?a ex:p ?x .
                BIND(year(?x) as ?year)
            }
        ",
        "
            @prefix ex: <https://example.com/> .
            @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

            input_graph(1, ex:p, \"2002-10-11T12:00:00-05:00\"^^xsd:dateTime) .
            input_graph(2, ex:p, \"-2002-11-10T12:00:01.555+05:00\") .
            input_graph(3, ex:p, 24) .
         ",
        "
            1, 2002
            2, UNDEF
            3, UNDEF
        "
    )
}

#[test]
fn bnode() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?bnode
            WHERE
            {
                ?a ex:p ?x .
                BIND(bnode() as ?bnode)
            }
        ",
        "
            @prefix ex: <https://example.com/> .
            @prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

            input_graph(1, ex:p, 2) .
            input_graph(2, ex:p, 2) .
         ",
        "
            1, _:0
            2, _:0
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
        "1, UNDEF; 2, \"de\""  // should be empty string instead of undef by standard
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

/// an alternative spelling for isIRI
#[test]
fn is_uri() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?iri
            WHERE
            {
                ex:s ex:p ?iri .
                FILTER(isURI(?iri))
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(ex:s, ex:p, ex:o) .
            input_graph(ex:s, ex:p, 2) .
         ",
        "<https://example.com/o>"
    )
}

#[test]
fn join() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?x
            WHERE
            {
                ?a ex:p ?x .
                ?a ex:q | ex:other ?x .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(1, ex:q, 11) .
            input_graph(2, ex:other, 22) .
            input_graph(3, ex:p, 33) .
            input_graph(4, ex:p, 44) .
            input_graph(4, ex:other, 44) .
         ",
        "1, 11; 4, 44"
    )
}


#[test]
fn join_undefined() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b ?x ?y
            WHERE
            {
                VALUES (?a ?b ?x) {(1 2 UNDEF) (UNDEF 3 4)}
                VALUES (?a ?b ?y) {(1 2 3) (1 3 5) (2 3 6) (UNDEF 3 7)}
            }
        ",
        "",
        "
            1, 2, UNDEF, 3
            1, 3, 4, 5
            2, 3, 4, 6
            UNDEF, 3, 4, 7
        "
    )
}


#[test]
fn join_multiple_undefined() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b ?c
            WHERE
            {
                VALUES (?a ?b ?c) {(UNDEF 2 3) (UNDEF 3 4)}
                VALUES (?a ?b ?c) {(1 2 3) (1 3 UNDEF) (2 3 4) (UNDEF 3 UNDEF) (2 3 6)}
            }
        ",
        "",
        "
            1, 2, 3
            1, 3, 4
            2, 3, 4
            UNDEF, 3, 4
        "
    )
}


#[test]
fn join_multi() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a ?b ?c
            WHERE
            {
                VALUES (?a ?b ?c) {(1 2 3) (1 2 3) (4 5 6) (7 8 9)}
                VALUES (?a ?b ?c) {(1 2 3) (1 2 3) (4 5 6) (4 5 6)}
            }
        ",
        "",
        "[
            1, 2, 3
            1, 2, 3
            1, 2, 3
            1, 2, 3
            4, 5, 6
            4, 5, 6
        ]"
    )
}


#[test]
fn join_multi_where_different_join_combinations_map_to_one() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a ?b ?c
            WHERE
            {
                VALUES (?a ?b ?c) {(UNDEF 2 3) (1 2 3) (4 5 6) (7 8 9)}
                VALUES (?a ?b ?c) {(1 2 3) (1 2 3) (4 5 6) (4 5 6)}
            }
        ",
        "",
        "[
            1, 2, 3
            1, 2, 3
            1, 2, 3
            1, 2, 3
            4, 5, 6
            4, 5, 6
        ]"
    )
}


#[test]
fn left_join() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?x ?a ?b
            WHERE
            {
                ?x ex:a ?a .
                OPTIONAL { ?x ex:b ?b } .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:a, 11) .
            input_graph(1, ex:b, 12) .
            input_graph(2, ex:other, 21) .
            input_graph(3, ex:a, 31) .
            input_graph(4, ex:a, 41) .
            input_graph(4, ex:b, 42) .
            input_graph(5, ex:a, 51) .
         ",
        "
            1, 11, 12
            3, 31, UNDEF
            4, 41, 42
            5, 51, UNDEF
        "
    )
}

#[test]
fn left_join_filter() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?x ?a ?b
            WHERE
            {
                ?x ex:a ?a .
                OPTIONAL {
                    ?x ex:b ?b
                    FILTER(?a > 11)
                } .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:a, 11) .
            input_graph(1, ex:b, 12) .
            input_graph(2, ex:other, 21) .
            input_graph(3, ex:a, 31) .
            input_graph(4, ex:a, 41) .
            input_graph(4, ex:b, 42) .
            input_graph(5, ex:a, 51) .
         ",
        "
            1, 11, UNDEF
            3, 31, UNDEF
            4, 41, 42
            5, 51, UNDEF
        "
    )
}


#[test]
fn left_join_filter_recursive() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?x ?b
            WHERE
            {
                ?x ex:a ?a .
                OPTIONAL {
                    ?x ex:b ?b
                    FILTER(?b < 10)
                }
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:a, 0) .
            input_graph(1, ex:b, 0) .
            input_graph(2, ex:a, 5) .
            input_graph(2, ex:b, 5) .
            input_graph(3, ex:a, 0) .
            input_graph(?n, ex:b, ?v + 1) :- projection(?n, ?v) .
            input_graph(3, ex:b, 0) :- projection(?n, ?v), ?n != 3, undefined_val(?v) .  % to fail more spectacularly
         ",
        "
            1, 0; 1, 1; 1, 2; 1, 3; 1, 4; 1, 5; 1, 6; 1, 7; 1, 8; 1, 9
            2, 5; 2, 6; 2, 7; 2, 8; 2, 9
            3, UNDEF
        "
    )
}

#[test]
fn left_join_positive_exists() -> Result<(), Error> {
    let sparql = "
        prefix ex: <https://example.com/>

        SELECT DISTINCT ?x ?a ?b
        WHERE
        {
            ?x ex:a ?a .
            OPTIONAL {
                ?x ex:b ?b .
                FILTER EXISTS { ?a ex:x ?b . }
            } .
        }
        ";
    assert_sparql(
        sparql,
        "
            @prefix ex: <https://example.com/> .

            input_graph(11, ex:x, 12) .
            input_graph(1, ex:a, 11) .
            input_graph(1, ex:b, 12) .
            input_graph(2, ex:other, 21) .
            input_graph(3, ex:a, 31) .
            input_graph(4, ex:a, 41) .
            input_graph(4, ex:b, 42) .
            input_graph(5, ex:a, 51) .
        ",
        "
            1, 11, 12
            3, 31, UNDEF
            4, 41, UNDEF
            5, 51, UNDEF
        "
    )
}


#[test]
fn left_join_multi_simple() -> Result<(), Error> {
    assert_sparql_multi(
        "
            prefix ex: <https://example.com/>

            SELECT ?x ?a ?b
            WHERE
            {
                ?x ex:a ?a .
                OPTIONAL { ?x ex:b ?b } .
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:a, 11) .
            input_graph(1, ex:b, 12) .
            input_graph(2, ex:other, 21) .
            input_graph(3, ex:a, 31) .
            input_graph(4, ex:a, 41) .
            input_graph(4, ex:b, 42) .
            input_graph(5, ex:a, 51) .
         ",
        "[
            1, 11, 12
            3, 31, UNDEF
            4, 41, 42
            5, 51, UNDEF
        ]"
    )
}

#[test]
fn left_join_multi() -> Result<(), Error> {
    assert_sparql_multi(
        "
            prefix ex: <https://example.com/>

            SELECT ?x ?y ?a ?b
            WHERE
            {
                VALUES (?x ?y ?a) {
                    (1 2 3) (1 2 3)
                    (1 3 5)
                    (1 UNDEF 6)
                    (2 3 UNDEF) (2 3 UNDEF) (2 3 UNDEF)
                }
                OPTIONAL { VALUES (?x ?y ?b) {
                    (1 2 4) (1 2 4) (1 2 4) (2 3 UNDEF) (2 3 UNDEF)
                } } .
            }
        ",
        "",
        "[
            1, 2, 3, 4; 1, 2, 3, 4; 1, 2, 3, 4; 1, 2, 3, 4; 1, 2, 3, 4; 1, 2, 3, 4
            1, 3, 5, UNDEF
            1, 2, 6, 4; 1, 2, 6, 4; 1, 2, 6, 4
            2, 3, UNDEF, UNDEF; 2, 3, UNDEF, UNDEF; 2, 3, UNDEF, UNDEF; 2, 3, UNDEF, UNDEF; 2, 3, UNDEF, UNDEF; 2, 3, UNDEF, UNDEF
        ]"
    )
}

#[test]
fn left_join_filter_multi() -> Result<(), Error> {
    assert_sparql_multi(
        "
            prefix ex: <https://example.com/>

            SELECT ?x ?y ?a ?b
            WHERE
            {
                VALUES (?x ?y ?a) {
                    (1 2 3)
                    (1 3 1)
                    (1 4 0)
                }
                OPTIONAL {
                    VALUES (?x ?y ?b) {
                        (1 2 4)
                        (1 3 0)
                        (1 4 ex:error_on_compare)
                    }
                    FILTER(?a < ?b)
                } .
            }
        ",
        "",
        "[
            1, 2, 3, 4
            1, 3, 1, UNDEF
            1, 4, 0, UNDEF
        ]"
    )
}

#[test]
fn left_join_positive_exists_multi() -> Result<(), Error> {
    let sparql = "
        prefix ex: <https://example.com/>

        SELECT ?x ?a ?b
        WHERE
        {
            ?x ex:a ?a .
            OPTIONAL {
                ?x ex:b ?b .
                FILTER EXISTS { ?a ex:x ?b . }
            } .
        }
        ";
    assert_sparql_multi(
        sparql,
        "
            @prefix ex: <https://example.com/> .

            input_graph(11, ex:x, 12) .
            input_graph(1, ex:a, 11) .
            input_graph(1, ex:b, 12) .
            input_graph(2, ex:other, 21) .
            input_graph(3, ex:a, 31) .
            input_graph(4, ex:a, 41) .
            input_graph(4, ex:b, 42) .
            input_graph(5, ex:a, 51) .
        ",
        "[
            1, 11, 12
            3, 31, UNDEF
            4, 41, UNDEF
            5, 51, UNDEF
        ]"
    )
}

#[test]
fn union() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?x
            WHERE
            {
                { ?a ex:p ?x . }
                UNION
                { ?a ex:q ?x . }
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:q, 22) .
            input_graph(3, ex:other, 33) .
            input_graph(4, ex:p, 44) .
            input_graph(5, ex:q, 55) .
         ",
        "1, 11; 2, 22; 4, 44; 5, 55"
    )
}

#[test]
fn union_unbound() -> Result<(), Error> {
    // unbound values are not implemented properly yet; this tests non-standard behaviour
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?x
            WHERE
            {
                { ?a ex:p ?x . }
                UNION
                { ?a ex:q ex:o . }
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 11) .
            input_graph(2, ex:q, ex:o) .
            input_graph(3, ex:other, 33) .
            input_graph(4, ex:p, 44) .
            input_graph(5, ex:q, ex:o) .
         ",
        "1, 11; 2, UNDEF; 4, 44; 5, UNDEF"
    )
}

#[test]
fn union_multi() -> Result<(), Error> {
    assert_sparql_multi(
        "
            prefix ex: <https://example.com/>

            SELECT ?x ?y ?a ?b
            WHERE
            {
                { VALUES (?x ?y ?a) {
                    (1 2 3)
                    (1 2 UNDEF)
                    (1 UNDEF UNDEF)
                    (UNDEF UNDEF UNDEF)
                } }
                UNION
                { VALUES (?x ?y ?b) {
                    (1 2 3)
                    (1 2 3)
                    (1 2 UNDEF)
                    (1 2 UNDEF)
                    (1 UNDEF UNDEF)
                    (UNDEF 2 UNDEF)
                    (UNDEF UNDEF UNDEF)
                } }
            }
        ",
        "",
        "[
            1, 2, 3, UNDEF
            UNDEF, 2, UNDEF, UNDEF

            1, 2, UNDEF, 3
            1, 2, UNDEF, 3
            1, UNDEF, UNDEF, UNDEF
            1, UNDEF, UNDEF, UNDEF
            UNDEF, UNDEF, UNDEF, UNDEF
            UNDEF, UNDEF, UNDEF, UNDEF

            1, 2, UNDEF, UNDEF
            1, 2, UNDEF, UNDEF
            1, 2, UNDEF, UNDEF
        ]"
    )
}



#[test]
fn union_seq() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?x ?y ?a ?b
            WHERE
            {
                { VALUES (?x ?y ?a) {
                    (1 2 3)
                    (1 2 UNDEF)
                    (1 UNDEF UNDEF)
                    (UNDEF UNDEF UNDEF)
                } }
                UNION
                { VALUES (?x ?y ?b) {
                    (1 2 3)
                    (1 2 3)
                    (1 2 UNDEF)
                    (1 2 UNDEF)
                    (1 UNDEF UNDEF)
                    (UNDEF 2 UNDEF)
                    (UNDEF UNDEF UNDEF)
                } }
            }
        ",
        "",
        "[
            1, 2, 3, UNDEF
            1, 2, UNDEF, UNDEF
            1, UNDEF, UNDEF, UNDEF
            UNDEF, UNDEF, UNDEF, UNDEF

            1, 2, UNDEF, 3
            1, 2, UNDEF, 3
            1, 2, UNDEF, UNDEF
            1, 2, UNDEF, UNDEF
            1, UNDEF, UNDEF, UNDEF
            UNDEF, 2, UNDEF, UNDEF
            UNDEF, UNDEF, UNDEF, UNDEF
        ]"
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
        "1, 5; 2, UNDEF"
    )
}

#[test]
fn bind_seq() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a ?y
            WHERE
            {
                ?a ex:p ?x .
                BIND(?x + ?x + ?x + ?x - ?a as ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 5) .
            input_graph(2, ex:p, 6) .
         ",
        "[1, 19; 2, 22]"
    )
}

#[test]
fn bind_seq_with_expression_error() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a ?y
            WHERE
            {
                ?a ex:p ?x .
                BIND(?x + ?x + ?x + ?x - ?a as ?y)
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 5) .
            input_graph(2, ex:p, ex:nan) .
         ",
        "[1, 19; 2, UNDEF]"
    )
}

#[test]
fn bind_multi_with_expression_error() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a ?y
            WHERE
            {
                {
                    ?a ex:p ?x .
                    BIND(?x + ?x + ?x + ?x - ?a as ?y)
                }
                VALUES (?a) { (1) (2) }
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:p, 5) .
            input_graph(2, ex:p, ex:nan) .
         ",
        "[1, 19; 2, UNDEF]"
    )
}

#[test]
fn minus() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                {
                    ?a ex:x ?b .
                    BIND(1 as ?c)
                }
                MINUS
                {
                    ?a ex:y ?b .
                    BIND(1 as ?d)
                }
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 5) .
            input_graph(1, ex:y, 5) .
            input_graph(2, ex:x, 5) .
            input_graph(2, ex:x, 6) .
            input_graph(2, ex:y, 6) .
            input_graph(3, ex:x, 7) .
         ",
        "2, 5; 3, 7"
    )
}

#[test]
fn minus_unbound() -> Result<(), Error> {
    // from sparql test suite
    assert_sparql(
        "
            prefix : <https://example.com/>

            select DISTINCT ?a ?b ?c {
              ?a a :Min
              OPTIONAL { ?a :p1 ?b }
              OPTIONAL { ?a :p2 ?c }
              MINUS {
                ?d a :Sub
                OPTIONAL { ?d :q1 ?b }
                OPTIONAL { ?d :q2 ?c }
              }
            }
        ",
        "
            @prefix ex: <https://example.com/> .
            @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .


            input_graph(ex:a1, rdf:type, ex:Min) .
            input_graph(ex:a1, ex:p1, ex:b1) .

            input_graph(ex:a2, rdf:type, ex:Min) .
            input_graph(ex:a2, ex:p1, ex:b2) .

            input_graph(ex:a3, rdf:type, ex:Min) .
            input_graph(ex:a3, ex:p1, ex:b3) .

            input_graph(ex:a4, rdf:type, ex:Min) .



            input_graph(ex:d1, rdf:type, ex:Sub) .
            input_graph(ex:d1, ex:q1, ex:b1) .

            input_graph(ex:d3, rdf:type, ex:Sub) .
            input_graph(ex:d3, ex:q1, ex:b3) .
            input_graph(ex:d3, ex:q2, ex:c3) .

            input_graph(ex:d4, rdf:type, ex:Sub) .
            input_graph(ex:d4, ex:q1, ex:b4) .
            input_graph(ex:d4, ex:q2, ex:c4) .

            input_graph(ex:d5, rdf:type, ex:Sub) .

         ",
        "<https://example.com/a2>, <https://example.com/b2>, UNDEF; <https://example.com/a4>, UNDEF, UNDEF"
    )
}

#[test]
fn values() -> Result<(), Error> {
    // note: values tuple with missing value in tuple is parsing error
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT *
            WHERE
            {
                VALUES (?a ?b ?c) {
                    (ex:a 1 2)
                    (ex:b UNDEF 3)
                    (ex:c 5 UNDEF)
                    (ex:a UNDEF UNDEF)
                }
            }
        ",
        "",
        "<https://example.com/a>, 1, 2; <https://example.com/b>, UNDEF, 3; <https://example.com/c>, 5, UNDEF; <https://example.com/a>, UNDEF, UNDEF"
    )
}

#[test]
fn project() -> Result<(), Error> {
    assert_sparql(
        "
            SELECT DISTINCT ?a ?c
            WHERE
            {
                VALUES (?a ?b ?c) {
                    (1 1 1)
                    (1 2 1)
                    (1 3 2)
                    (1 4 UNDEF)
                }
            }
        ",
        "",
        "1, 1; 1, 2; 1, UNDEF"
    )
}

#[test]
fn project_seq() -> Result<(), Error> {
    assert_sparql(
        "
            SELECT ?a ?c
            WHERE
            {
                VALUES (?a ?b ?c) {
                    (1 1 1)
                    (1 3 2)
                    (1 2 1)
                    (1 4 UNDEF)
                }
            }
        ",
        "",
        "[1, 1; 1, 2; 1, 1; 1, UNDEF]"
    )
}


#[test]
fn project_multi() -> Result<(), Error> {
    assert_sparql(
        "
            SELECT ?a ?c
            WHERE
            {
                VALUES (?a) { (1) }
                VALUES (?a ?b ?c) {
                    (1 1 1)
                    (1 3 2)
                    (1 2 1)
                    (1 4 UNDEF)
                }
            }
        ",
        "",
        "[1, 1; 1, 1; 1, 2; 1, UNDEF]"
    )
}


#[test]
fn project_undef() -> Result<(), Error> {
    assert_sparql(
        "
            SELECT ?x ?a ?c ?y
            WHERE
            {
                VALUES (?a) { (1) }
                VALUES (?a ?b ?c) {
                    (1 1 1)
                    (1 3 2)
                    (1 2 1)
                    (1 4 UNDEF)
                }
            }
        ",
        "",
        "[
            UNDEF, 1, 1, UNDEF
            UNDEF, 1, 1, UNDEF
            UNDEF, 1, 2, UNDEF
            UNDEF, 1, UNDEF, UNDEF
        ]"
    )
}

#[test]
fn order_by_irrelevant() -> Result<(), Error> {
    // order by has no effect in this example
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a ex:x ?b
                {
                    SELECT ?a ?b
                    WHERE { ?a ex:x ?b }
                    ORDER BY DESC(?b)
                }
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 2) .
            input_graph(2, ex:x, 3) .
        ",
        "1, 2; 2, 3"
    )
}

#[test]
fn limit() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a ex:x ?b
            }
            LIMIT 2
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 11) .
            input_graph(2, ex:x, 22) .
            input_graph(3, ex:x, 33) .
            input_graph(4, ex:x, 44) .
        ",
        "1, 11; 2, 22"
    )
}

#[test]
fn limit_nested() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                BIND(1 as ?x)
                {
                    SELECT DISTINCT ?a ?b
                    WHERE { ?a ex:x ?b }
                    LIMIT 2
                }
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 11) .
            input_graph(2, ex:x, 22) .
            input_graph(3, ex:x, 33) .
            input_graph(4, ex:x, 44) .
        ",
        "1, 11; 2, 22"
    )
}



#[test]
fn limit_sequence() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a ?b
            WHERE
            {
                ?a ex:x ?b
            }
            LIMIT 2
            OFFSET 1
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 11) .
            input_graph(2, ex:x, 22) .
            input_graph(3, ex:x, 33) .
            input_graph(4, ex:x, 44) .
        ",
        "[2, 22; 3, 33]"
    )
}


#[test]
fn offset() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a ?b
            WHERE
            {
                ?a ex:x ?b
            }
            OFFSET 2
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 11) .
            input_graph(2, ex:x, 22) .
            input_graph(3, ex:x, 33) .
            input_graph(4, ex:x, 44) .
        ",
        "3, 33; 4, 44"
    )
}

#[test]
fn group_by() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT ?a (SUM(DISTINCT ?b + 1) as ?s) (COUNT(DISTINCT ?b) as ?c)
            WHERE
            {
                ?a ex:x ?b
            }
            GROUP BY ?a
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 10) .
            input_graph(1, ex:x, 11) .
            input_graph(2, ex:x, 20) .
            input_graph(2, ex:x, 21) .
        ",
        "1, 23, 2; 2, 43, 2"
    )
}

#[test]
fn count_star() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT DISTINCT (COUNT(DISTINCT *) as ?c)
            WHERE
            {
                ?a ex:x ?b
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 10) .
            input_graph(1, ex:x, 11) .
            input_graph(2, ex:x, 20) .
            input_graph(2, ex:x, 21) .
        ",
        "4"
    )
}

#[test]
fn reduced() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT REDUCED ?a ?b
            WHERE
            {
                ?a ex:x ?b
            }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 10) .
            input_graph(1, ex:x, 11) .
        ",
        "[1, 10; 1, 11]"
    )
}

#[test]
fn order_by() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a ?b
            WHERE
            {
                ?a ex:x ?b
            }
            ORDER BY DESC(-?b) ?a
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 1) .
            input_graph(1, ex:x, 2) .
            input_graph(2, ex:x, 0) .
            input_graph(3, ex:x, 0) .
        ",
        "[2, 0; 3, 0; 1, 1; 1, 2]"
    )
}


#[test]
fn order_by_multi_type() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            SELECT ?a ?b
            WHERE
            {
                VALUES (?a ?b) {
                    (\"o\" 0)
                    (\"o\" 4)
                    (\"q\" 0)

                    (1 \"abc\")
                    (\"o\" \"xyz\")
                    (ex:a \"abc\")

                    (-1 0.3e0)
                    (10000 4.3e0)
                    (-2 0.3e0)
                }
            }
            ORDER BY DESC(-?b) ?a
        ",  // note that strings are Error when negated hence sorting by ?a in first three rows
        "",
        "[
            <https://example.com/a>, \"abc\"
            1, \"abc\"
            \"o\", \"xyz\"
            \"o\", 0
            \"q\", 0
            -2, \"0.3\"^^<http://www.w3.org/2001/XMLSchema#double>
            -1, \"0.3\"^^<http://www.w3.org/2001/XMLSchema#double>
            \"o\", 4
            10000, \"4.3\"^^<http://www.w3.org/2001/XMLSchema#double>
        ]"
    )
}


#[test]
fn describe() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            DESCRIBE ?x ?o <https://example.com/x>
            WHERE    {?x ex:x ?o}
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 1) .
            input_graph(1, ex:x, 2) .
            input_graph(2, ex:x, 0) .
            input_graph(3, ex:y, 0) .
            input_graph(ex:x, ex:x, 6) .
        ",
        "
            1, <https://example.com/x>, 1
            1, <https://example.com/x>, 2
            2, <https://example.com/x>, 0
            <https://example.com/x>, <https://example.com/x>, 6
        "
    )
}

#[test]
fn ask() -> Result<(), Error> {
    let t = "\"true\"^^<http://www.w3.org/2001/XMLSchema#boolean>";
    let f = "\"false\"^^<http://www.w3.org/2001/XMLSchema#boolean>";
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            ASK {?x ex:x ex:o}
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 1) .
            input_graph(1, ex:x, ex:o) .
            input_graph(12, ex:x, ex:o) .
        ",
        t
    )?;
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            ASK {?x ex:x ex:o}
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(1, ex:x, 1) .
            input_graph(1, ex:x, ex:p) .
            input_graph(12, ex:y, ex:o) .
        ",
        f
    )?;
    Ok(())
}


#[test]
fn construct() -> Result<(), Error> {
    assert_sparql(
        "
            prefix ex: <https://example.com/>

            CONSTRUCT WHERE {_:1 ex:x ?a . ?a ex:y _:1 . ex:a ex:b ex:c . }
        ",
        "
            @prefix ex: <https://example.com/> .

            input_graph(ex:s, ex:x, 1) .
            input_graph(1, ex:y, ex:s) .
            input_graph(ex:s, ex:x, ex:o) .
            input_graph(ex:o, ex:y, ex:s) .
            input_graph(ex:s, ex:z, ex:o) .
            input_graph(ex:o, ex:z, ex:s) .
            input_graph(ex:a, ex:b, ex:c) .
        ",
        "
            _:1, <https://example.com/x>, 1
            _:0, <https://example.com/x>, <https://example.com/o>
            <https://example.com/o>, <https://example.com/y>, _:0
            <https://example.com/a>, <https://example.com/b>, <https://example.com/c>
        "
    )
}
