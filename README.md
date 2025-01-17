# SPARQL2NEMO Converter
Transforms a given [SPARQL query](https://www.w3.org/TR/sparql11-query/) to [NEMO](https://github.com/knowsys/nemo) code. 
The program works by transforming operations of the SPARQL algebra recursively. 
Translation to SPARQL algebra uses [spargebra](https://docs.rs/spargebra/latest/spargebra/) which is developed as part of the 
[oxigraph](https://docs.rs/oxigraph/latest/oxigraph/) graph database.

## Supported Features
Translation implementations for SPARQL Features can be found in [translation.rs](src/translation.rs).
Functions are generally named after the SPARQL algebra operation they translate. 

There are special suffixes for functions that do not produce solution sets:
- `*_seq` for solution sequence: first position of resulting predicate is index in solution sequence
- `*_multi` for solution multiset (a.k.a. unordered solution sequence): first position of resulting predicate is multiplicity
- `*_g` for generic implementations supporting multiple types of solutions
- `*_multi_g` for generic implementations supporting solution multiset and regular solution sets
- `*_seq_g` for generic implementations supporting solution sequences and regular solutions sets

You may also look at the example queries in [tests.rs](src/tests.rs).

## Usage
There is no explicit UI. 
The output NEMO program is printed to stdout and needs to be combined with the graph data and executed manually. 
The input graph is currently provided in NEMO as the ternary predicate `input_graph(?subject, ?predicate, ?object)`.

Select a mode by calling the desired function in [main()](src/main.rs):
- `_test_translation()`: Converts a SPARQL query (supplied as `query_str`) to NEMO program
- `_test_parsing()`: Converts a SPARQL query (`query_str`) to SPARQL algebra
- `_test_rust()`: For trying out some Rust features
- `_test_model()`: For trying out the Rust macro based NEMO templating language
- `_translate_stdin()`: For reading SPARQL query from stdin printing NEMO translation to stdout

Run the code using:
```bash
cargo +nightly run
```

You may need to install the following packages if you don't have them already (Ubuntu):
```bash
sudo apt update
sudo apt install pkg-config
sudo apt install libssl-dev
```

Tests need to be run with `RUST_TEST_THREADS=1` environment variable because Nemo uses timing locks where it is unknown 
how multithreading is supported with this.

### Translate queries from stdin
- Ensure the `_translate_stdin()` function is called in main.
- Build using `cargo +nightly build --release`
- Use using `echo "ASK {?a ?b ?c}" | ./target/release/sparql2nemo`
- Translation is written to stdout
