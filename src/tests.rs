use std::collections::HashSet;
use nemo::datavalues::AnyDataValue;
use nemo::error::Error;
use nemo::execution::{DefaultExecutionEngine, ExecutionEngine};
use nemo::io::ImportManager;
use nemo::io::parser::parse_program;
use nemo::io::resource_providers::ResourceProviders;
use crate::translation_next::translate;

fn execute_nemo(program_string: String) -> Result<Vec<Vec<AnyDataValue>>, Error> {
    let program = parse_program(program_string)?;
    let import_manager = ImportManager::new(ResourceProviders::from(vec![]));
    let mut engine: DefaultExecutionEngine = ExecutionEngine::initialize(&program, import_manager)?;
    engine.execute()?;
    let mut output_iterator = program.output_predicates();
    let output_predicate = output_iterator.next().expect("program has no output");
    assert_eq!(output_iterator.next(), None, "program has more than one output");
    let output = engine.predicate_rows(output_predicate)?.expect("output not defined");
    Ok(output.collect())
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