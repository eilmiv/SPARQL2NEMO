use std::collections::HashMap;
use std::fmt::Debug;
use spargebra::algebra::{AggregateExpression, Expression, Function, GraphPattern, OrderExpression, PropertyPathExpression};
use spargebra::Query;
use spargebra::term::{BlankNode, GroundTerm, Literal, NamedNode, NamedNodePattern, TermPattern, TriplePattern, Variable};
use crate::error::TranslateError;
use crate::error::TranslateError::{AggregationNotImplemented, MultiPatternNotImplemented, PatternNotImplemented, SequencePatternNotImplemented};
use crate::nemo_model::{add_rule, Binding, BoundPredicate, Call, construct_program, get_vars, has_prop_for_var, hash_dedup, nemo_add, nemo_atoms, nemo_call, nemo_condition, nemo_def, nemo_filter, nemo_iri, nemo_predicate_type, nemo_terms, nemo_var, PredicatePtr, ProtoPredicate, Rule, TermSet, to_bound_predicate, to_negated_bound_predicate, TypedPredicate, VarPtr};

nemo_predicate_type!(SolutionSet = ...);
nemo_predicate_type!(SolutionMultiSet = count ...);
nemo_predicate_type!(SolutionSequence = index ...);
nemo_predicate_type!(SolutionExpression = ... result);

/// Flag for property of predicate position to never be undefined.
const IS_DEFINED: u32 = 1 << 0;

/// namespaces
const XSD: &str = "http://www.w3.org/2001/XMLSchema#";

impl SolutionExpression {
    fn depend_vars(&self) -> Vec<VarPtr> {
        let vars = self.get_predicate().vars();
        vars[..vars.len() - 1].iter().map(|v| v.clone()).collect()
    }

    fn result_var(&self) -> VarPtr {
        let vars = self.get_predicate().vars();
        vars.last().expect("expression needs to have result").clone()
    }

    fn mark_nullable(&self) {
        let vars = self.get_predicate().vars();
        self.get_predicate().unset_property(IS_DEFINED, vars.len() - 1);
    }
}

impl SolutionSet {
    fn from_predicate(p: &PredicatePtr) -> SolutionSet {
        SolutionSet{inner: p.clone()}
    }
}

impl From<&NamedNode> for Binding {
    fn from(value: &NamedNode) -> Self {
        Binding::Constant(value.to_string())
    }
}

impl From<&Literal> for Binding {
    fn from(value: &Literal) -> Self {
        Binding::Constant(value.to_string())
    }
}

struct VariableTranslator {
    variable_cache: HashMap<String, VarPtr>
}

impl VariableTranslator {
    fn new() -> VariableTranslator {
        VariableTranslator {variable_cache: HashMap::new()}
    }

    fn get(&mut self, var: &Variable) -> VarPtr {
        self.variable_cache
            .entry(var.to_string())
            .or_insert_with(|| VarPtr::new(var.as_str()))
            .clone()
    }

    fn bnode(&mut self, bnode: &BlankNode) -> VarPtr {
        let id = bnode.as_str();
        self.variable_cache
            .entry(bnode.to_string())
            .or_insert_with(|| VarPtr::new(&format!("BNODE_VARIABLE_{id}")))
            .clone()
    }
}

struct QueryTranslator {
    sparql_vars: VariableTranslator,
    input_graph: PredicatePtr,
    undefined_val: SolutionExpression,
}

impl QueryTranslator {
    fn new(input_graph: PredicatePtr) -> QueryTranslator {
        let human_readable_undef = true;
        let undefined_val = if human_readable_undef {
            nemo_def!(undefined_val(nemo_iri!(UNDEF)) :- {nemo_atoms![]}; SolutionExpression);
            undefined_val
        } else {
            let some_bnode = nemo_var!(!undef);
            nemo_def!(undefined_val(some_bnode) :- {nemo_atoms![]}; SolutionExpression);
            undefined_val
        };
        undefined_val.mark_nullable();

        QueryTranslator{sparql_vars: VariableTranslator::new(), input_graph, undefined_val}
    }

    fn triple_set(&self) -> SolutionSet {
        SolutionSet::from_predicate(&self.input_graph)
    }

    fn translate_var_func(&mut self) -> impl FnMut(&Variable) -> VarPtr + '_ {
        move |var: &Variable| self.sparql_vars.get(var)
    }

    /// maps all variables of target that are not in source to unbound
    fn map_unbound(&self, target: &dyn TypedPredicate, source: &dyn TypedPredicate) -> (BoundPredicate, Vec<VarPtr>) {
        let unbound = VarPtr::new("unbound");
        let unbound_predicate = BoundPredicate::new(self.undefined_val.get_predicate(), vec![Binding::from(&unbound)], false);
        let vars = get_vars(target).iter().map(|v| if get_vars(source).contains(v) {v.clone()} else {unbound.clone()} ).collect::<Vec<_>>();
        (unbound_predicate, vars)
    }

    /// info
    /// - still stratified even tho it includes negation
    fn translate_expression_variable(&mut self, var: &Variable, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let var_binding = self.sparql_vars.get(var);
        if get_vars(binding).contains(&var_binding) {
            let undef = self.undefined_val.clone();
            nemo_def!(var(var_binding; @result: var_binding) :- binding(??set_contains_var), ~undef(var_binding); SolutionExpression);
            Ok(var)
        }
        else {
            let always_error = SolutionExpression::create("always_error", vec![var_binding.clone()]);
            Ok(always_error)
        }
    }

    fn translate_expression_named_node(&mut self, node: &NamedNode) -> Result<SolutionExpression, TranslateError> {
        let named_node = SolutionExpression::create("named_node", vec![VarPtr::new("result")]);
        nemo_add!(named_node(node.clone()));
        Ok(named_node)
    }

    fn translate_expression_literal(&mut self, node: &Literal) -> Result<SolutionExpression, TranslateError> {
        let named_node = SolutionExpression::create("literal", vec![VarPtr::new("result")]);
        nemo_add!(named_node(node.clone()));
        Ok(named_node)
    }

    fn translate_or(&mut self, left: &SolutionExpression, right: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let or = SolutionExpression::create("or", nemo_terms![left.depend_vars(), right.depend_vars(), VarPtr::new("result")].vars());
        nemo_add!(or(??left, ??right; @result: true) :- left(??left; @result: true), binding(??left, ??right, ??other));
        nemo_add!(or(??left, ??right; @result: true) :- right(??right; @result: true), binding(??left, ??right, ??other));
        nemo_add!(or(??both, ??left, ??right; @result: false) :- left(??both, ??left; @result: false), right(??both, ??right; @result: false), binding(??both, ??left, ??right, ??other));
        Ok(or)
    }

    fn translate_and(&mut self, left: &SolutionExpression, right: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let and = SolutionExpression::create("and", nemo_terms![left.depend_vars(), right.depend_vars(), VarPtr::new("result")].vars());
        nemo_add!(and(??left, ??right; @result: false) :- left(??left; @result: false), binding(??left, ??right, ??other));
        nemo_add!(and(??left, ??right; @result: false) :- right(??right; @result: false), binding(??left, ??right, ??other));
        nemo_add!(and(??both, ??left, ??right; @result: true) :- left(??both, ??left; @result: true), right(??both, ??right; @result: true), binding(??both, ??left, ??right, ??other));
        Ok(and)
    }

    fn translate_not(&mut self, inner: &SolutionExpression) -> Result<SolutionExpression, TranslateError> {
        let b = nemo_var!(b);
        nemo_def!(boolean_not(??not_vars; @result: nemo_call!(NOT; b)) :- inner(??not_vars; @result: b); SolutionExpression);
        Ok(boolean_not)
    }

    fn translate_by_cases(&mut self, true_filter: ProtoPredicate, false_filter: ProtoPredicate, left: &SolutionExpression, right: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        nemo_def!(
            bool_by_cases(??both, ??left, ??right; @result: true) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { true_filter }
                ; SolutionExpression
        );
        nemo_add!(
            bool_by_cases(??both, ??left, ??right; @result: false) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { false_filter }
        );
        Ok(bool_by_cases)
    }

    /// info
    /// - true and false should never both apply
    fn translate_comparison(&mut self, true_op: &str, false_op: &str, str_compare: i32, str_compare_for: bool, left: &SolutionExpression, right: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError>{
        // numeric
        nemo_def!(
            comparison(??both, ??left, ??right; @result: true) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { nemo_condition!(?l, true_op, ?r) }
                ; SolutionExpression
        );
        nemo_add!(
            comparison(??both, ??left, ??right; @result: false) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { nemo_condition!(?l, false_op, ?r)  }
        );

        // boolean
        let l = nemo_var!(l);
        let r = nemo_var!(r);
        nemo_add!(
            comparison(??both, ??left, ??right; @result: true) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: l),
                right(??both, ??right; @result: r),
                { nemo_condition!(nemo_call!(INT; l), true_op, nemo_call!(INT; r)) },
                { nemo_condition!(nemo_call!(DATATYPE; l), " = ", nemo_iri!(XSD => boolean))},
                { nemo_condition!(nemo_call!(DATATYPE; r), " = ", nemo_iri!(XSD => boolean))}
        );
        nemo_add!(
            comparison(??both, ??left, ??right; @result: false) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: l),
                right(??both, ??right; @result: r),
                { nemo_condition!(nemo_call!(INT; l), false_op, nemo_call!(INT; r)) },
                { nemo_condition!(nemo_call!(DATATYPE; l), " = ", nemo_iri!(XSD => boolean))},
                { nemo_condition!(nemo_call!(DATATYPE; r), " = ", nemo_iri!(XSD => boolean))}
        );

        // string
        nemo_add!(
            comparison(??both, ??left, ??right; @result: str_compare_for) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: l),
                right(??both, ??right; @result: r),
                { nemo_condition!(nemo_call!(COMPARE; l, r), " = ", str_compare) }
        );
        nemo_add!(
            comparison(??both, ??left, ??right; @result: !str_compare_for) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: l),
                right(??both, ??right; @result: r),
                { nemo_condition!(nemo_call!(COMPARE; l, r), " != ", str_compare) }
        );
        Ok(comparison)
    }

    fn translate_equal(&mut self, left: &SolutionExpression, right: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError>{
        // numeric
        nemo_def!(
            equal(??both, ??left, ??right; @result: true) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { nemo_condition!(?l, " >= ", ?r) },
                { nemo_condition!(?l, " <= ", ?r) }
                ; SolutionExpression
        );
        nemo_add!(
            equal(??both, ??left, ??right; @result: false) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { nemo_condition!(?l, " > ", ?r) }
        );
        nemo_add!(
            equal(??both, ??left, ??right; @result: false) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { nemo_condition!(?l, " < ", ?r) }
        );

        // non numeric
        nemo_add!(
            equal(??both, ??left, ??right; @result: true) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { nemo_condition!(?l, " = ", ?r) },
                { nemo_filter!("AND(isNumeric(", ?l, "), isNumeric(", ?r, ")) = ", false, "")}
        );
        nemo_add!(
            equal(??both, ??left, ??right; @result: false) :-
                binding(??both, ??left, ??right, ??other),
                left(??both, ??left; @result: ?l),
                right(??both, ??right; @result: ?r),
                { nemo_condition!(?l, " != ", ?r) },
                { nemo_filter!("AND(isNumeric(", ?l, "), isNumeric(", ?r, ")) = ", false, "")}
        );
        Ok(equal)
    }

    /// info:
    /// - Equality should be done for different types, but is not. See https://www.w3.org/TR/sparql11-query/#OperatorMapping
    ///     - datetime not supported
    ///     - some conversions not supported e.g. int to double!
    /// - handles zero length list correctly
    /// - errors may be hidden if thing is in list or may propagate (this is correct)
    ///     - divide by zero produces error correctly; infinity panics -> bad
    /// - Expressions never produce unbound results, therefore no handling of unbound (unbound == error)
    fn translate_in(&mut self, inner: &SolutionExpression, list: &Vec<SolutionExpression>, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        // FALSE CASE
        let mut false_conditions = nemo_atoms![];
        for expr in list {
            false_conditions = nemo_atoms![false_conditions, expr, nemo_condition!(expr.result_var(), " != ", inner.result_var())]
        }
        nemo_def!(
            in_expression(nemo_terms!(inner.depend_vars(), list => SolutionExpression::depend_vars, false))
            :- {binding}, {inner}, {false_conditions}
            ; SolutionExpression
        );

        // TRUE CASES
        for expr in list {
            nemo_add!(
                in_expression(??both, ??iner, ??expr, ??remaining; @result: true) :-
                    binding(??both, ??iner, ??expr, ??remaining, ??other),
                    inner(??both, ??iner; @result: ?r),
                    expr(??both, ??expr; @result: ?r)
            );
        }

        Ok(in_expression)
    }

    /// info
    /// - "... all operators operate on RDF Terms and will produce a type error if any arguments are unbound."
    ///     - this is ensured by expressions never producing unbound results
    fn translate_binary_operator(&mut self, l: Binding, r: Binding, result: Binding, left_solution: &SolutionExpression, right_solution: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError>{
        nemo_def!(
            op(??vars, ??left, ??right; @result: result) :-
                binding(??var, ??left, ??right, ??other),
                left_solution(??vars, ??left; @result: l),
                right_solution(??vars, ??right; @result: r)
                ; SolutionExpression
        );
        Ok(op)
    }

    fn translate_positive_exists(&mut self, pattern_solution: &SolutionSet, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        nemo_def!(partial_exists(??intersection; @result: true) :- pattern_solution(??intersection, ??pattern_only), binding(??intersection, ??other); SolutionExpression);
        Ok(partial_exists)
    }

    /// info
    /// - Consider current bindings to restrict and therefore optimize inner pattern for EXISTS
    fn translate_exists(&mut self, pattern_solution: &SolutionSet, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let partial_exists = self.translate_positive_exists(pattern_solution, binding)?;
        nemo_def!(exists(??vars; @result: true) :- partial_exists(??vars; @result: true); SolutionExpression);
        nemo_add!(exists(??vars; @result: false) :- binding(??vars, ??other), ~partial_exists(??vars; @result: true));
        Ok(exists)
    }

    fn translate_bound(&mut self, var: &Variable, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let nemo_var = self.sparql_vars.get(var);
        let unbound = self.undefined_val.clone();
        nemo_def!(bound(nemo_var; @result: true) :- binding(??vars), ~unbound(nemo_var); SolutionExpression);
        if !has_prop_for_var(binding, IS_DEFINED, &nemo_var) {
            // it is important to add this rule only if nemo_var is not known to be defined because it marks it as possibly undefined
            nemo_add!(bound(nemo_var; @result: false) :- unbound(nemo_var), binding(??vars));
        }
        Ok(bound)
    }

    /// info:
    /// - this behaves exactly as if only one branch would ever be evaluated
    /// - an error in the condition results in an error
    fn translate_if(&mut self, condition: &SolutionExpression, true_val: &SolutionExpression, false_val: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let vars = nemo_terms!(condition.depend_vars(), true_val.depend_vars(), false_val.depend_vars(), VarPtr::new("result")).vars();
        let if_expression = SolutionExpression::create("if_expression", vars);
        nemo_add!(
            if_expression(??all, ??cond, ??val, ??extra; @result: ?v) :-
                binding(??all, ??cond, ??val, ??extra, ??other),
                condition(??all, ??cond; @result: true),
                true_val(??all, ??val; @result: ?v)
        );
        nemo_add!(
            if_expression(??all, ??cond, ??val, ??extra; @result: ?v) :-
                binding(??all, ??cond, ??val, ??extra, ??other),
                condition(??all, ??cond; @result: false),
                false_val(??all, ??val; @result: ?v)
        );
        Ok(if_expression)
    }

    fn translate_coalesce(&mut self, expressions: Vec<SolutionExpression>, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let mut not_previous_success = nemo_atoms![];
        let coalesce = SolutionExpression::create("coalesce", nemo_terms![&expressions => SolutionExpression::depend_vars, VarPtr::new("result")].vars());

        for expr in expressions {
            let tmp = not_previous_success.flat_clone();
            nemo_add!(coalesce(nemo_terms!(get_vars(&coalesce))) :- {binding}, expr(??expr_vars; @result: coalesce.result_var()), {not_previous_success});
            not_previous_success = nemo_atoms![tmp, &to_negated_bound_predicate(&expr)];
        }

        Ok(coalesce)
    }

    /// info
    /// - would be false for invalid literals and NaN, but nemo has no invalid literals or NaN
    /// - effective boolean value calculation for named nodes (IRIs) and all other nodes are type errors
    /// - special handling because no automatic float-int conversion, current implementation
    fn translate_effective_boolean_value(&mut self, expression: &SolutionExpression) -> Result<SolutionExpression, TranslateError> {
        // bools
        nemo_def!(effective_boolean_value(??vars; @result: false) :- expression(??vars; @result: ?v), {nemo_filter!("", ?v, " = ", false, "")}; SolutionExpression);
        nemo_add!(effective_boolean_value(??vars; @result: true) :- expression(??vars; @result: ?v), {nemo_filter!("", ?v, " = ", true, "")});

        // strings
        nemo_add!(effective_boolean_value(??vars; @result: false) :- expression(??vars; @result: ?v), {nemo_filter!("STRLEN(", ?v, ") = 0")});
        nemo_add!(effective_boolean_value(??vars; @result: true) :- expression(??vars; @result: ?v), {nemo_filter!("STRLEN(", ?v, ") > 0")});

        // numbers
        nemo_add!(effective_boolean_value(??vars; @result: false) :- expression(??vars; @result: ?v), {nemo_condition!(?v, " >= ", 0)}, {nemo_condition!(?v, " <= ", 0)});
        nemo_add!(effective_boolean_value(??vars; @result: true) :- expression(??vars; @result: ?v), {nemo_condition!(?v, " > ", 0)});
        nemo_add!(effective_boolean_value(??vars; @result: true) :- expression(??vars; @result: ?v), {nemo_condition!(?v, " < ", 0)});

        Ok(effective_boolean_value)
    }

    fn expression_known_to_be_bool(expr: &Expression) -> bool {
        if let Expression::Literal(l) = expr {
            if l.datatype() == spargebra::term::Literal::from(true).datatype() {
                return true
            }
        }
        match expr {
            Expression::Equal(_, _) | Expression::SameTerm(_, _) |
            Expression::Greater(_, _) | Expression::GreaterOrEqual(_, _) |
            Expression::Less(_, _) | Expression::LessOrEqual(_, _) |
            Expression::In(_, _) | Expression::Exists(_) | Expression::Bound(_) |
            Expression::Not(_) | Expression::Or(_, _) | Expression::And(_, _) |
            Expression::FunctionCall(Function::IsBlank, _) |
            Expression::FunctionCall(Function::IsNumeric, _) |
            Expression::FunctionCall(Function::IsIri, _) |
            Expression::FunctionCall(Function::IsLiteral, _) => true,
            _ => false
        }
    }

    fn translate_bool_expression(&mut self, expression: &Expression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let mut result = self.translate_expression(expression, binding)?;
        if !Self::expression_known_to_be_bool(expression) {result = self.translate_effective_boolean_value(&result)?}
        Ok(result)
    }

    fn function(&mut self, expressions: &Vec<SolutionExpression>, binding: &dyn TypedPredicate, func: &str) -> Result<SolutionExpression, TranslateError> {
        let call = Call::new(func, nemo_terms!(expressions => SolutionExpression::result_var).bindings());
        nemo_def!(solution(nemo_terms!(expressions => SolutionExpression::depend_vars, call)) :- {expressions}, {binding}; SolutionExpression; &func.to_lowercase());
        Ok(solution)
    }

    /// info:
    /// - Note negative years exist -> pass the reversed date string
    /// - seconds should be decimal not double
    /// - possibly handling of ill formed literals
    fn date_function(&mut self, expressions: &Vec<SolutionExpression>, func: &Function, parameter_expressions: &Vec<Expression>) -> Result<SolutionExpression, TranslateError> {
        let (is_time, offset) = match func {
            Function::Year => (false, 2),
            Function::Month => (false, 1),
            Function::Day => (false, 0),
            Function::Hours => (true, 0),
            Function::Minutes => (true, 1),
            Function::Seconds => (true, 2),
            _ => Err(TranslateError::FunctionNotImplemented(func.clone()))?
        };
        if expressions.len() != 1 {Err(TranslateError::InvalidNumberOfArguments(func.clone(), parameter_expressions.clone()))?}
        let date = expressions.get(0).unwrap();

        let var = nemo_var!(date);
        let mut call = nemo_call!(STR; var);
        let mut separator = "-";
        if is_time {
            call = nemo_call!(STRAFTER; call, "T");
            separator = ":";
        } else {
            call = nemo_call!(STRBEFORE; call, "T");
            call = nemo_call!(STRREV; call);
        }
        let mut offset_counter = offset;
        while offset_counter > 0 { call = nemo_call!(STRAFTER; call, separator); offset_counter -= 1;}
        if offset < 2 {call = nemo_call!(STRBEFORE; call, separator);}
        if !is_time {call = nemo_call!(STRREV; call);}
        if is_time && offset == 2 {
            // parse seconds seconds
            // remove time zone
            call = nemo_call!(STRBEFORE; nemo_call!(CONCAT; call, "+"), "+");
            call = nemo_call!(STRBEFORE; nemo_call!(CONCAT; call, "-"), "-");
            call = nemo_call!(STRBEFORE; nemo_call!(CONCAT; call, "Z"), "Z");
            call = nemo_call!(DOUBLE; call);
        } else {
            call = nemo_call!(INT; call);
        }
        nemo_def!(extract_date(??vars; @result: call) :- date(??vars; @result: var), {nemo_condition!(nemo_call!(DATATYPE; var), " = ", nemo_iri!(XSD => dateTime))}; SolutionExpression);
        Ok(extract_date)
    }

    /// info
    /// - "Apart from BOUND, COALESCE, NOT EXISTS and EXISTS, all functions and operators operate on RDF Terms and will produce a type error if any arguments are unbound." -> because expressions never return undef
    /// - "Any expression other than logical-or (||) or logical-and (&&) that encounters an error will produce that error." -> yes because failing to bind expression inputs is error
    /// - round function is not standard compliant
    /// - bnode creation would be possible -> only without parameters
    ///     - creates only single fact with is consistent with blazegraph, also when part of a larger expression that uses other variables (Virtuoso raises "Built-in function is not implemented")
    /// - lang does not return "" on simple literal
    /// - preserving lang and xsd:string vs plain string not implemented in nemo
    /// - SUBSTR parameters are derived int in SPARQL and nemo but double in XPath
    /// - sum, min, max work in theory on xs:anyAtomicType for sum at least this means that there must be the case of error and so maybe not supporting everything is ok
    /// - there is fn:reverse however those work on sequences and SPARQL defines to translate to call on sequence of "single node" and there is even an example:
    ///     - fn:reverse(("hello")) returns ("hello").
    /// - considerations about STRLEN
    fn translate_function(&mut self, func: &Function, parameter_expressions: &Vec<Expression>, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let params = parameter_expressions.iter().map(|e| self.translate_expression(e, binding)).collect::<Result<Vec<_>, _>>()?;
        match func {
            Function::Str => self.function(&params, binding, "STR"),
            Function::Lang => self.function(&params, binding, "LANG"),
            // LangMatches -> language tag matches a lang range e.g. en-US, de-*
            Function::Datatype => self.function(&params, binding, "DATATYPE"),
            // Iri
            // StrLang -> constructs lang string
            // StrDt -> constructs literal with datatype
            Function::BNode => {
                if params.is_empty() {
                    nemo_def!(bnode(nemo_var!(!bnode)) :- {nemo_atoms![]}; SolutionExpression);
                    Ok(bnode)
                } else {Err(TranslateError::FunctionNotImplemented(func.clone()))}
            },
            // Rand
            Function::Abs => self.function(&params, binding, "ABS"),
            Function::Ceil => self.function(&params, binding, "CEIL"),
            Function::Floor => self.function(&params, binding, "FLOOR"),
            Function::Round => self.function(&params, binding, "ROUND"),
            Function::Concat => self.function(&params, binding, "CONCAT"),
            Function::SubStr => self.function(&params, binding, match params.len() {
                2 => "SUBSTR",
                3 => "SUBSTRING",
                _ => Err(TranslateError::InvalidNumberOfArguments(func.clone(), parameter_expressions.clone()))?
            }),
            Function::StrLen => self.function(&params, binding, "STRLEN"),
            // Replace -> supports regex
            Function::UCase => self.function(&params, binding, "UCASE"),
            Function::LCase => self.function(&params, binding, "LCASE"),
            // EncodeForUri
            Function::Contains => self.function(&params, binding, "CONTAINS"),
            Function::StrStarts => self.function(&params, binding, "STRSTARTS"),
            Function::StrEnds => self.function(&params, binding, "STRENDS"),
            Function::StrBefore => self.function(&params, binding, "STRBEFORE"),
            Function::StrAfter => self.function(&params, binding, "STRAFTER"),
            Function::Year | Function::Month | Function::Day | Function::Hours | Function::Minutes | Function::Seconds => self.date_function(&params, func, parameter_expressions),
            // Timezone -> timezone as dayTimeDuration
            // Tz -> timezone as simple literal
            // Now
            // Uuid, StrUuid
            // Md5, Sha1, Sha256, Sha384, Sha512
            Function::IsIri => self.function(&params, binding, "isIri"),
            Function::IsBlank => self.function(&params, binding, "isNull"),
            Function::IsLiteral => {
                let is_iri = self.function(&params, binding, "isIri")?;
                let is_blank = self.function(&params, binding, "isNull")?;
                let either = self.function(&vec![is_iri, is_blank], binding, "OR")?;
                self.function(&vec![either], binding, "NOT")
            }
            Function::IsNumeric => self.function(&params, binding, "isNumeric"),
            Function::Regex => self.function(&params, binding, "REGEX"),
            // Triple, Subject, Predicate, Object, IsTriple
            // Adjust -> no clue what this is
            Function::Custom(func_iri) => {
                match func_iri.as_str() {
                    "http://www.w3.org/2005/xpath-functions/math#sqrt" => self.function(&params, binding, "SQRT"),
                    "http://www.w3.org/2005/xpath-functions/math#sin" => self.function(&params, binding, "SIN"),
                    "http://www.w3.org/2005/xpath-functions/math#cos" => self.function(&params, binding, "COS"),
                    "http://www.w3.org/2005/xpath-functions/math#tan" => self.function(&params, binding, "TAN"),
                    // "http://www.w3.org/2005/xpath-functions/math#log" => self.function(&params, binding, "LOG"), // no IRI for log x base y known
                    "http://www.w3.org/2005/xpath-functions/math#pow" => self.function(&params, binding, "POW"),
                    // rem
                    "https://www.w3.org/2005/xpath-functions#sum" => self.function(&params, binding, "SUM"),
                    // prod
                    "https://www.w3.org/2005/xpath-functions#min" => self.function(&params, binding, "MIN"),
                    "https://www.w3.org/2005/xpath-functions#max" => self.function(&params, binding, "MAX"),
                    // luka
                    // bitand
                    // bitor
                    // bitxor
                    // STRREV
                    _ => Err(TranslateError::FunctionNotImplemented(func.clone()))
                }
            }
            _ => Err(TranslateError::FunctionNotImplemented(func.clone()))
        }
    }

    /// info:
    /// - nemos AND and OR functions handle errors not correctly
    /// - same term normalizes first
    /// - nemo has no unary operators -> implement anyway but can not use them because there might be strings
    /// - divide produces always int but is decimal in SPARQL when dividing ints
    /// - comparisons
    ///     - comparisons explicitly implemented for strings
    ///     - inputs not casted for equality but for less, greater and others they are (nemo just converts different types to double)
    ///     - converting to double seems to be equivalent to the numeric type promotion and subtype substitution rules for less, greater and those operators
    ///     - dateTime, boolean not supported (boolean can not even be converted to double, but it is converted to int)
    ///     - special handling of conversion for equality
    fn translate_expression(&mut self, expression: &Expression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        match expression {
            Expression::Variable(v) => self.translate_expression_variable(v, binding),
            Expression::NamedNode(n) => self.translate_expression_named_node(n),
            Expression::Literal(l) => self.translate_expression_literal(l),
            Expression::Or(left, right) => {
                let left_solution = self.translate_bool_expression(left, binding)?;
                let right_solution = self.translate_bool_expression(right, binding)?;
                self.translate_or(&left_solution, &right_solution, binding)
            },
            Expression::And(left, right) => {
                let left_solution = self.translate_bool_expression(left, binding)?;
                let right_solution = self.translate_bool_expression(right, binding)?;
                self.translate_and(&left_solution, &right_solution, binding)
            },
            Expression::Not(inner) => {
                let inner_solution = self.translate_bool_expression(inner, binding)?;
                self.translate_not(&inner_solution)
            },
            Expression::SameTerm(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_by_cases(
                    nemo_filter!("fullStr(", ?l, ") = fullStr(", ?r, ")"),
                    nemo_filter!("fullStr(", ?l, ") != fullStr(", ?r, ")"),
                    &left_solution, &right_solution, binding
                )
            },
            Expression::Greater(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_comparison(
                    " > ", " <= ", 1, true, &left_solution, &right_solution, binding
                )
            },
            Expression::GreaterOrEqual(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_comparison(
                    " >= ", " < ", -1, false, &left_solution, &right_solution, binding
                )
            },
            Expression::Less(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_comparison(
                    " < ", " >= ", -1, true, &left_solution, &right_solution, binding
                )
            },
            Expression::LessOrEqual(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_comparison(
                    " <= ", " > ", 1, false, &left_solution, &right_solution, binding
                )
            },
            Expression::Equal(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_equal(&left_solution, &right_solution, binding)
            },
            Expression::In(inner, list) => {
                let inner_solution = self.translate_expression(inner, binding)?;
                let solution_list = list.into_iter().map(|e| self.translate_expression(e, binding)).collect::<Result<Vec<_>, _>>()?;
                self.translate_in(&inner_solution, &solution_list, binding)
            },
            Expression::Add(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                let l = nemo_var!(l);
                let r = nemo_var!(r);
                self.translate_binary_operator(l.clone(), r.clone(), l + r, &left_solution, &right_solution, binding)
            }
            Expression::Subtract(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                let l = nemo_var!(l);
                let r = nemo_var!(r);
                self.translate_binary_operator(l.clone(), r.clone(), l - r, &left_solution, &right_solution, binding)
            }
            Expression::Multiply(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                let l = nemo_var!(l);
                let r = nemo_var!(r);
                self.translate_binary_operator(l.clone(), r.clone(), l * r, &left_solution, &right_solution, binding)
            }
            Expression::Divide(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                let l = nemo_var!(l);
                let r = nemo_var!(r);
                self.translate_binary_operator(l.clone(), r.clone(), l / r, &left_solution, &right_solution, binding)
            }
            Expression::UnaryPlus(inner) => {
                let inner_solution = self.translate_expression(inner, binding)?;
                let r = nemo_var!(r);
                nemo_def!(unary_plus(??vars; @result: 0 + r.clone()) :- binding(??vars, ??other), inner_solution(??vars; @result: r); SolutionExpression);
                Ok(unary_plus)
            }
            Expression::UnaryMinus(inner) => {
                let inner_solution = self.translate_expression(inner, binding)?;
                let r = nemo_var!(r);
                nemo_def!(unary_minus(??vars; @result: 0 - r.clone()) :- binding(??vars, ??other), inner_solution(??vars; @result: r); SolutionExpression);
                Ok(unary_minus)
            }
            Expression::Exists(pattern) => {
                let pattern_solution = self.translate_pattern(pattern)?;
                self.translate_exists(&pattern_solution, binding)
            },
            Expression::Bound(var) => {
                self.translate_bound(var, binding)
            },
            Expression::If(cond, true_val, false_val) => {
                let cond_solution = self.translate_bool_expression(cond, binding)?;
                let true_solution = self.translate_expression(true_val, binding)?;
                let false_solution = self.translate_expression(false_val, binding)?;
                self.translate_if(&cond_solution, &true_solution, &false_solution, binding)
            }
            Expression::Coalesce(vals) => {
                let val_solutions = vals.iter().map(|v| self.translate_expression(v, binding)).collect::<Result<Vec<_>, _>>()?;
                self.translate_coalesce(val_solutions, binding)
            }
            Expression::FunctionCall(func, params) => self.translate_function(func, params, binding)
        }
    }


    fn translate_term(&mut self, term: &TermPattern, variables: &mut Vec<VarPtr>, bnode_vars: &mut Vec<VarPtr>) -> Result<Binding, TranslateError> {
        #[allow(unreachable_patterns)]
        Ok(match term {
            TermPattern::NamedNode(node) => Binding::from(node),
            TermPattern::Literal(node) => Binding::from(node),
            TermPattern::BlankNode(node) => {
                let var = self.sparql_vars.bnode(node);
                bnode_vars.push(var.clone());
                Binding::from(var)
            },
            TermPattern::Variable(var) => {
                let var = self.sparql_vars.get(var);
                variables.push(var.clone());
                Binding::from(var)
            },
            _ => unreachable!("Sub triples not enabled")
        })
    }

    fn translate_triple(&mut self, triple: &TriplePattern, variables: &mut Vec<VarPtr>, bnode_vars: &mut Vec<VarPtr>) -> Result<BoundPredicate, TranslateError>{
        let subject = self.translate_term(&triple.subject, variables, bnode_vars)?;
        let predicate = match &triple.predicate {
            NamedNodePattern::NamedNode(node) => Binding::from(node),
            NamedNodePattern::Variable(var) => {
                let var = self.sparql_vars.get(var);
                variables.push(var.clone());
                Binding::from(var)
            }
        };
        let object = self.translate_term(&triple.object, variables, bnode_vars)?;
        Ok(BoundPredicate::new(self.input_graph.clone(), vec![subject, predicate, object], false))
    }

    /// info
    /// - mapping variables is µ, bnodes is sigma and both is called "Pattern Instance Mapping"
    /// - note that bnodes are projected away and can never match anything in the future
    ///     - this is standard compliant because the algebra returns just solution mappings µ
    ///     - however e.g. in rdflib bnodes can match across joins: `list(g.query("select ?c where {{_:1 a ?c}{_:1 a ?d . BIND(?d as ?c)}}"))`
    ///         - note that without BIND the two parts would be a single graph pattern and the bnodes could indeed interact
    ///             - I did not find this in the standard, might be spargebra specific optimization
    ///     - spargebra produces a parsing error in this case
    fn translate_bgp(&mut self, patterns: &Vec<TriplePattern>) -> Result<SolutionSet, TranslateError> {
        let mut variables = Vec::new();
        let mut body_parts = nemo_atoms![];
        for triple in patterns {
            body_parts = nemo_atoms![body_parts, &self.translate_triple(triple, &mut variables, &mut vec![])?];
        }
        nemo_def!(bgp(nemo_terms!(variables)) :- {body_parts}; SolutionSet);
        Ok(bgp)
    }

    fn translate_bgp_multi(&mut self, patterns: &Vec<TriplePattern>) -> Result<SolutionMultiSet, TranslateError> {
        let mut variables = Vec::new();
        let mut bnode_vars = Vec::new();
        let mut body_parts = nemo_atoms![];
        for triple in patterns {
            body_parts = nemo_atoms![body_parts, &self.translate_triple(triple, &mut variables, &mut bnode_vars)?];
        }
        if bnode_vars.is_empty() {
            nemo_def!(bgp(@count: 1; nemo_terms!(variables)) :- {body_parts}; SolutionMultiSet);
            Ok(bgp)
        } else {
            nemo_def!(bgp(@count: %count(nemo_terms!(bnode_vars)); nemo_terms!(variables)) :- {body_parts}; SolutionMultiSet);
            Ok(bgp)
        }
    }

    fn is_constant(b: &Binding) -> bool {
        match b {
            Binding::Constant(_c) => true,
            Binding::Variable(_v) => false,
            _ => panic!("this function should only be called with variables or constants")
        }
    }

    /// info
    /// - path iteration could probably restrict inner path more (only compute inner path for actually needed)
    ///     - could add optional restricting predicate for start and end of each path function
    ///     - note that two hop (quadratic size) is not computed for inner path
    /// - works similar to function ALP in standard
    ///     - the binding that is not a constant forms the visited term set in ALP
    ///         - reverse iterate is actually part of ZeroOrMorePath definition not ALP
    ///         - the start node is not part of the set
    ///     - nemo recursion replaces recursion in function
    ///     - visited check by nemos set semantic
    fn translate_one_or_more_path(&mut self, start: Binding, path: &SolutionSet, end: Binding) -> SolutionSet {
        let reverse_iterate = Self::is_constant(&end) && !Self::is_constant(&start);
        let mid = nemo_var!(mid);
        if reverse_iterate {
            nemo_def!(reverse_recursive(?next, end) :- path(?next, end); SolutionSet);
            nemo_add!(reverse_recursive(?next, end) :- path(?next, mid), reverse_recursive(mid, end));
            nemo_def!(one_or_more_path(start, end) :- reverse_recursive(start, end); SolutionSet);
            one_or_more_path
        }
        else {
            nemo_def!(recursive(start, ?next) :- path(start, ?next); SolutionSet);
            nemo_add!(recursive(start, ?next) :- recursive(start, mid), path(mid, ?next));
            nemo_def!(one_or_more_path(start, end) :- recursive(start, end); SolutionSet);
            one_or_more_path
        }
    }

    /// info:
    /// - "Node set of a graph" only includes subject and object
    /// - check if start and end are different constants is NOT done using spargebra (in)equality operator for terms to ensure consistency when path gets simplified to bgp
    ///     - a problem even tho standard does not allow literal in subject position.
    ///     - what about `select distinct (1 as ?out) where {1 (^<https://example.com/backward> / <https://example.com/forward>)? 1}`
    ///         - error in virtuoso (literal in subject position of transitive triple pattern)
    ///         - 1 and 1.0 considered different in blazegraph and rdflib, however "01"^^xsd:integer and "1"^^xsd:integer are only different in rdflib
    /// - this literally changes the path, not relevant but example of needing to be carefull when to check for UNDEF pos in precicate
    fn zero_path_extend(&mut self, start: Binding, path: SolutionSet, end: Binding) -> SolutionSet {
        // start and end are different constants -> there is no zero path
        if Self::is_constant(&start) && Self::is_constant(&end) {
            nemo_def!(start_c(start));
            nemo_def!(end_c(end));
            nemo_add!(path(?c, ?c) :- start_c(?c), end_c(?c));
            return path
        }

        let start_constant = if Self::is_constant(&start) {Some(start)} else {None};
        let end_constant = if Self::is_constant(&end) {Some(end)} else {None};
        let constant = start_constant.or(end_constant);

        if let Some(c) = constant {
            // one term, the other one is a variable; two terms already handled above
            nemo_add!(path(c, c));
        }
        else {
            // no constants
            let input_graph = self.triple_set();
            nemo_add!(path(?s, ?s) :- input_graph(?s, ?p, ?o));
            nemo_add!(path(?o, ?o) :- input_graph(?s, ?p, ?o));
        }
        path
    }

    /// info
    /// - only matches forward properties is correct: https://www.w3.org/TR/sparql11-query/#eval_negatedPropertySet
    fn translate_negated_property_set(&mut self, start: Binding, properties: &Vec<NamedNode>, end: Binding) -> SolutionSet {
        let mut filters = nemo_atoms!();
        for p in properties {
            filters = nemo_atoms!(filters, nemo_condition!(?property, " != ", p.clone()));
        }
        let graph = self.triple_set();
        nemo_def!(negated_property_set(start, end) :- graph(start, ?property, end), {filters}; SolutionSet);
        negated_property_set
    }

    /// info
    /// - bnodes in path expression start or end
    ///     - `select distinct (1 as ?out) where {_:1 (^<https://example.com/backward> / <https://example.com/forward>)? _:1}`
    ///     - rdflib/blazegraph has no result
    ///     - virtuoso has error: bnode not allowed in subject of transitive path (like literal)
    ///     - works for me but parsing error when bnode occurs also in normal bgp
    ///         - except for anonomous bnodes: s:a s:b [ s:x* s:y ] !
    /// - zero length path between node not in data is treated as existing I this is correct, easyer to see for ZeroOrOne than for ZeroOrMore path
    /// - returned predicate has always two variables, in the standard there can be a solution mapping with one variable this is represented by binding one variable always to a constant
    fn translate_path(&mut self, start: Binding, path: &PropertyPathExpression, end: Binding) -> Result<SolutionSet, TranslateError> {
        match path {
            PropertyPathExpression::NamedNode(property) => {
                let input_graph = self.triple_set();
                nemo_def!(path_property(start, end) :- input_graph(start, property.clone(), end); SolutionSet);
                Ok(path_property)
            },
            PropertyPathExpression::Reverse(p) => {
                let inner = self.translate_path(end.clone(), p, start.clone())?;
                nemo_def!(path_reverse(start, end) :- inner(end, start); SolutionSet);
                Ok(path_reverse)
            }
            PropertyPathExpression::Sequence(first_path, second_path) => {
                let middle = nemo_var!(path_middle);
                let first = self.translate_path(start.clone(), first_path, middle.clone())?;
                let second = self.translate_path(middle.clone(), second_path, end.clone())?;
                nemo_def!(path_sequence(start, end) :- first(start, middle), second(middle, end); SolutionSet);
                Ok(path_sequence)
            }
            PropertyPathExpression::Alternative(first_path, second_path) => {
                let first = self.translate_path(start.clone(), first_path, end.clone())?;
                let second = self.translate_path(start.clone(), second_path, end.clone())?;
                nemo_def!(path_alternative(start, end) :- first(start, end); SolutionSet);
                nemo_add!(path_alternative(start, end) :- second(start, end));
                Ok(path_alternative)
            }
            PropertyPathExpression::OneOrMore(p) => {
                let inner = self.translate_path(nemo_var!(start), p, nemo_var!(end))?;
                Ok(self.translate_one_or_more_path(start, &inner, end))
            }
            PropertyPathExpression::ZeroOrMore(p) => {
                let inner = self.translate_path(nemo_var!(start), p, nemo_var!(end))?;
                let one_or_more = self.translate_one_or_more_path(start.clone(), &inner, end.clone());
                Ok(self.zero_path_extend(start, one_or_more, end))
            }
            PropertyPathExpression::ZeroOrOne(p) => {
                let inner = self.translate_path(start.clone(), p, end.clone())?;
                Ok(self.zero_path_extend(start, inner, end))
            }
            PropertyPathExpression::NegatedPropertySet(properties) => {
                Ok(self.translate_negated_property_set(start, properties, end))
            }
        }
    }

    /// binds unbound values in with_undef to all possible values in bindings_from
    fn bind_unbound(&mut self, with_undef: &SolutionSet, bindings_from: &SolutionSet) -> (ProtoPredicate, TermSet) {
        let mut map_atoms = nemo_atoms![];
        let mut new_binding = nemo_terms![];
        for v in get_vars(with_undef) {
            if get_vars(bindings_from).contains(&v) && !has_prop_for_var(with_undef, IS_DEFINED, &v) {
                let maybe_undef = nemo_var!(maybe_undef);
                let undef = self.undefined_val.clone();
                nemo_def!(map(v, maybe_undef) :- {bindings_from}, undef(maybe_undef); SolutionSet);
                nemo_add!(map(v, v) :- {with_undef});
                map_atoms = nemo_atoms![map_atoms, &map];
                new_binding = nemo_terms![new_binding, maybe_undef];
            } else {
                new_binding = nemo_terms![new_binding, v]
            }
        }
        (map_atoms, new_binding)
    }

    /// info:
    /// - different join algorithms possible (maybe prove equivalence?)
    fn translate_join(&mut self, left: &SolutionSet, right: &SolutionSet) -> Result<SolutionSet, TranslateError> {
        let result_terms = nemo_terms![get_vars(left), get_vars(right)];
        let (left_map_atoms, left_bindings) = self.bind_unbound(left, right);
        let (right_map_atoms, right_bindings) = self.bind_unbound(right, left);
        nemo_def!(join(result_terms) :- {left_map_atoms}, left(left_bindings), {right_map_atoms}, right(right_bindings); SolutionSet);
        Ok(join)
    }

    /// notes
    /// - changed left join to call the filter also on the unbound variables, is this correct?
    /// 	- changed back because filtered values should probably lead to unbound values
    /// - could optimize left join to not do unbound variables if all variables match (but probably mostly they don't)
    /// - cross join for non overlapping ?
    /// - handle join like/using normal join
    ///
    /// info:
    /// - did not require negation with existential rules (however existential rules are unreliable)
    /// . consider all cases: identical variables, overlapping variables, non overlapping variables
    fn translate_left_join(&mut self, left: &Box<GraphPattern>, right: &Box<GraphPattern>, expression: &Option<Expression>) -> Result<SolutionSet, TranslateError> {
        let left_solution = self.translate_pattern(left)?;
        let right_solution = self.translate_pattern(right)?;

        // regular join
        nemo_def!(raw_join(??both, ??left, ??right) :- left_solution(??both, ??left), right_solution(??both, ??right); SolutionSet);

        // filtering
        let filtered_join = match expression {
            Some(Expression::Exists(pattern)) => {
                let pattern_solution = self.translate_pattern(pattern)?;
                let expression_solution = self.translate_positive_exists(&pattern_solution, &raw_join)?;
                self.translate_filter(&expression_solution, &raw_join)?
            }
            Some(e) => {
                let expression_solution = self.translate_bool_expression(e, &raw_join)?;
                self.translate_filter(&expression_solution, &raw_join)?
            },
            None => raw_join
        };

        // add unbound values
        nemo_def!(left_join(??vars) :- filtered_join(??vars); SolutionSet);
        let (unbound, head) = self.map_unbound(&left_join, &left_solution);
        nemo_add!(left_join(head) :- left_solution(??left), ~filtered_join(??left, ??right_only), {&unbound});

        Ok(left_join)
    }

    fn translate_filter(&mut self, expression: &SolutionExpression, inner: &SolutionSet) -> Result<SolutionSet, TranslateError> {
        nemo_def!(filter(??expr_vars, ??other_vars) :- inner(??expr_vars, ??other_vars), expression(??expr_vars; @result: true); SolutionSet);
        Ok(filter)
    }

    /// info:
    /// - in a simple world without unbound variables this could also just work on compatible bindings
    fn translate_union(&mut self, left: &SolutionSet, right: &SolutionSet) -> Result<SolutionSet, TranslateError> {
        let union = SolutionSet::create("union", nemo_terms![get_vars(left), get_vars(right)].vars());
        let (left_unbound, left_head) = self.map_unbound(&union, left);
        let (right_unbound, right_head) = self.map_unbound(&union, right);
        nemo_add!(union(left_head) :- left(??left), {&left_unbound});
        nemo_add!(union(right_head) :- right(??right), {&right_unbound});
        Ok(union)
    }

    /// notes
    /// - Test what others do when binding to an already existing variable
    /// - optimize for known functions that do not error
    /// info:
    /// - old implementation with null as unbound using existential rule did not require negation
    fn translate_extend(&mut self, inner: &SolutionSet, var: &Variable, expression: &SolutionExpression) -> Result<SolutionSet, TranslateError> {
        let bound_var = self.sparql_vars.get(var);
        let unbound = self.undefined_val.clone();
        nemo_def!(extend(??e_vars, ??base_vars, bound_var) :- inner(??e_vars, ??base_vars), expression(??e_vars; @result: bound_var); SolutionSet);
        nemo_add!(extend(??e_vars, ??base_vars, ?unbound) :- inner(??e_vars, ??base_vars), ~expression(??e_vars; @result: bound_var), unbound(?unbound));
        Ok(extend)
    }

    fn translate_ground_term(&mut self, term: &Option<GroundTerm>, undef_var: &Binding) -> Binding {
        #[allow(unreachable_patterns)]
        match term {
            None => undef_var.clone(),
            Some(GroundTerm::Literal(l)) => Binding::from(l),
            Some(GroundTerm::NamedNode(n)) => Binding::from(n),
            _ => unreachable!("rdf* feature is not enabled")
        }
    }

    /// info
    /// - used empty rule because exitentials only work with rules
    /// - existentials could loose some tuples that also exist with all UNDEFs bound
    fn translate_values(&mut self, variables: &Vec<Variable>, bindings: &Vec<Vec<Option<GroundTerm>>>) -> SolutionSet {
        let values = SolutionSet::create("values", nemo_terms!(variables => self.translate_var_func()).vars());
        let undef = nemo_var!(undef);
        let undef_pred = self.undefined_val.clone();
        for binding in bindings {
            let terms: Vec<Binding> = binding.iter().map(|b| self.translate_ground_term(b, &undef)).collect();
            nemo_add!(values(terms) :- undef_pred(undef));
        }
        values
    }

    /// notes
    /// - this is wrong for multi sets, you might have to combine things that become the same after projection
    fn translate_project_g<T: TypedPredicate>(&mut self, inner: &T, variables: &Vec<Variable>) -> Result<T, TranslateError> {
        nemo_def!(projection(@?count: ?c, @?index: ?i; nemo_terms!(variables => self.translate_var_func())) :- inner(@?count: ?x, @?index: ?i; ??all_vars); T);
        Ok(projection)
    }

    fn translate_slice_seq(&mut self, inner: &SolutionSequence, start: usize, length: Option<usize>) -> SolutionSequence {
        let index = nemo_var!(index);
        let mut condition = nemo_condition!(index, " >= ", start);
        if let Some(l) = length {
            condition = nemo_atoms![condition, nemo_condition!(index, " < ", start + l)]
        }
        nemo_def!(slice(@index: index.clone() - start; ??vars) :- inner(@index: index; ??vars), {condition}; SolutionSequence);
        slice
    }

    fn translate_slice(&mut self, inner: &SolutionSet, start: usize, length: Option<usize>) -> SolutionSet {
        let inner_sequence = self.get_sequence(inner);
        let slice_sequence = self.translate_slice_seq(&inner_sequence, start, length);
        nemo_def!(slice_set(??vars) :- slice_sequence(@index: ?i; ??vars); SolutionSet);
        slice_set
    }

    fn translate_aggregation(&mut self, inner: &dyn TypedPredicate, variable: VarPtr, expression: &Expression, aggregation: &str, group_vars: &Vec<VarPtr>, idempotent: bool) -> Result<SolutionSet, TranslateError>{
        let expr_solution = self.translate_expression(expression, inner)?;

        let aggregate_vars = if idempotent {
            nemo_terms![expr_solution.result_var()]
        } else {
            let inner_vars: Vec<_> = get_vars(inner).into_iter().filter(|v| !group_vars.contains(v)).collect();
            nemo_terms![expr_solution.result_var(), inner_vars]
        };
        let aggregate = SolutionSet::create(&format!("{aggregation}_aggregate"), nemo_terms![group_vars, variable].vars());
        let aggregation_call = Call::new(&format!("#{aggregation}"), aggregate_vars.bindings());
        nemo_add!(aggregate(??group_vars, aggregation_call) :- inner(??group_vars, ??other), {&expr_solution});
        Ok(aggregate)
    }

    /// note
    /// - count(*) with all variables grouped results in count in nemo without parameters -> error
    /// - is count(*) with all variables grouped valid sparql? currently crashes
    fn translate_count_all(&mut self, inner: &dyn TypedPredicate, variable: VarPtr, group_vars: Vec<VarPtr>) -> Result<SolutionSet, TranslateError> {
        let aggregate_vars: Vec<VarPtr> = get_vars(inner).iter().filter(|v| !group_vars.contains(v)).map(|v| v.clone()).collect();
        let aggregation_call = Call::new("#count", aggregate_vars.iter().map(Binding::from).collect());
        let count_all = SolutionSet::create("count_all", group_vars.into_iter().chain(vec![variable]).collect());
        nemo_add!(count_all(??group_vars, aggregation_call) :- inner(??group_vars, ??other));
        Ok(count_all)
    }

    /// notes
    /// - Note: aggregation somewhat different in spargebra vs. SPARQL semantic
    /// - Implement remaining aggregations
    /// - Think about error during aggregation
    /// - Implement non distinct aggregations
    fn translate_group_by(&mut self, inner: &SolutionSet, group_vars: &Vec<Variable>, aggregates: &Vec<(Variable, AggregateExpression)>) -> Result<SolutionSet, TranslateError> {
        let collect_aggregations = SolutionSet::create(
            "collect_aggregations",
            group_vars.iter().chain(aggregates.iter().map(|(v, _a)| v)).map(|v| self.sparql_vars.get(v)).collect()
        );
        let mut body = vec![to_bound_predicate(inner)];
        for (variable, aggregation) in aggregates {
            let var = self.sparql_vars.get(variable);
            let group_by_vars = group_vars.iter().map(|v| self.sparql_vars.get(v)).collect();
            let aggregation_solution = match aggregation {
                AggregateExpression::Count {expr: None, distinct: true} => self.translate_count_all(inner, var, group_by_vars),
                AggregateExpression::Count {expr: Some(expr), distinct: true} => self.translate_aggregation(inner, var, expr, "count", &group_by_vars, false),
                AggregateExpression::Sum {expr, distinct: true} => self.translate_aggregation(inner, var, expr, "sum", &group_by_vars, false),
                AggregateExpression::Min {expr, distinct: true} => self.translate_aggregation(inner, var, expr, "min", &group_by_vars, true),
                AggregateExpression::Max {expr, distinct: true} => self.translate_aggregation(inner, var, expr, "max", &group_by_vars, true),
                _ => Err(AggregationNotImplemented(aggregation.clone()))
            }?;
            body.push(to_bound_predicate(&aggregation_solution));
        }
        add_rule(&collect_aggregations, Rule::new(get_vars(&collect_aggregations).iter().map(Binding::from).collect(), body, vec![]));
        Ok(collect_aggregations)
    }

    /// a stable sort
    /// notes
    /// - Undefined sorted first
    /// - sort assumes total order
    /// - implement fast hacker sort for benchmarking
    fn translate_sort(&mut self, inner: &SolutionSequence, order_expression: &OrderExpression) -> Result<SolutionSequence, TranslateError> {
        let val = nemo_var!(sort_val);
        let other_val = nemo_var!(other_sort_val);
        let index = nemo_var!(index);
        let other_index = nemo_var!(other_index);
        let (filter, expression) = match order_expression {
            OrderExpression::Asc(e) => (nemo_condition!(other_val, " <= ", val), e),
            OrderExpression::Desc(e) => (nemo_condition!(other_val, " >= ", val), e),
        };

        let expression_solution = self.translate_expression(expression, inner)?;
        nemo_def!(sort_condition(?i, ??both, ??depend; @result: ?r) :- inner(@index: ?i; ??both, ??depend), expression_solution(??depend; @result: ?r); SolutionExpression);
        nemo_def!(sorted_proto(@index: %count(other_index); ??vars) :- sort_condition(?i, ??vars; @result: val), sort_condition(other_index, ??*other_vars; @result: other_val), {filter}; SolutionSequence);

        let index_filter = nemo_condition!(other_index, " >= ", index);
        nemo_def!(sorted_ties(@index: %count(other_index); ??vars) :- sort_condition(index, ??vars; @result: ?r), sort_condition(other_index, ??*other_vars; @result: ?r), {index_filter}; SolutionSequence);
        nemo_def!(sorted(@index: index.clone() - other_index.clone(); ??vars) :- sorted_proto(@index: index; ??vars), sorted_ties(@index: other_index; ??vars); SolutionSequence);
        Ok(sorted)
    }

    fn translate_order_by_seq(&mut self, inner: &SolutionSequence, expressions: &Vec<OrderExpression>) -> Result<SolutionSequence, TranslateError> {
        let mut solution = inner.clone();
        for expression in expressions.iter().rev() {
            solution = self.translate_sort(&solution, expression)?;
        }
        Ok(solution)
    }

    fn get_multi(&mut self, inner: &SolutionSet) -> SolutionMultiSet {
        nemo_def!(multi(@count: 1; ??vars) :- inner(??vars); SolutionMultiSet);
        multi
    }

    /// notes
    /// - get_sequence uses hacky bit (could be replaced by sort in the future)
    /// - implement sorting based variant
    fn get_sequence(&mut self, inner: &SolutionSet) -> SolutionSequence {
        nemo_def!(sequence_proto(??vars; @result: nemo_var!(!bnode_for_id)) :- inner(??vars); SolutionExpression);
        let bnode_var = nemo_var!(bnode_var);
        let id_var = nemo_var!(id);
        let min_var = nemo_var!(min);
        nemo_def!(sequence_shifted(??vars; @result: nemo_call!(INT; nemo_call!(STR; bnode_var))) :- sequence_proto(??vars; @result: bnode_var); SolutionExpression);
        nemo_def!(sequence_start(%min(?id)) :- sequence_shifted(??vars; @result: ?id); SolutionSet);
        nemo_def!(sequence(@index: id_var.clone() - min_var.clone(); ??vars) :- sequence_shifted(??vars; @result: id_var.clone()), sequence_start(min_var.clone()); SolutionSequence);
        sequence
    }

    /// notes
    /// - get_sequence_from_multi uses relatively slow iteration
    fn get_sequence_from_multi(&mut self, inner: &SolutionMultiSet) -> SolutionSequence {
        let remaining = nemo_var!(remaining);
        nemo_def!(pre_index(??vars, remaining.clone() - 1) :- inner(@count: remaining.clone(); ??vars); SolutionSet);
        nemo_add!(pre_index(??vars, remaining.clone() - 1) :- pre_index(??vars, remaining.clone()), {nemo_filter!("", remaining.clone(), " > 0")});
        let pre_sequence = self.get_sequence(&pre_index);
        nemo_def!(sequence(@index: ?i; ??vars) :- pre_sequence(@index: ?i; ??vars, remaining); SolutionSequence);
        sequence
    }

    fn get_multi_from_sequence(&mut self, inner: &SolutionSequence) -> SolutionMultiSet {
        nemo_def!(as_multi(@count: %count(?i); ??vars) :- inner(@index: ?i; ??vars); SolutionMultiSet);
        as_multi
    }

    /// notes
    /// - Handle non overlapping domain for Minus
    fn translate_pattern(&mut self, pattern: &GraphPattern) -> Result<SolutionSet, TranslateError> {
        match pattern {
            GraphPattern::Bgp {patterns} => self.translate_bgp(patterns),
            GraphPattern::Path{subject, path, object} => {
                let start = self.translate_term(subject, &mut vec![], &mut vec![])?;
                let end = self.translate_term(object, &mut vec![], &mut vec![])?;
                self.translate_path(start, path, end)
            },
            GraphPattern::Join{left, right} => {
                let left_solution = self.translate_pattern(left)?;
                let right_solution = self.translate_pattern(right)?;
                self.translate_join(&left_solution, &right_solution)
            }
            GraphPattern::LeftJoin {left, right, expression} => {
                self.translate_left_join(left, right, expression)
            }
            GraphPattern::Filter {expr: Expression::Exists(pattern), inner} => {
                let inner_solution = self.translate_pattern(inner)?;
                let exists_solution = self.translate_pattern(pattern)?;
                let expr_solution = self.translate_positive_exists(&exists_solution, &inner_solution)?;
                self.translate_filter(&expr_solution, &inner_solution)
            },
            GraphPattern::Filter {expr, inner} => {
                let inner_solution = self.translate_pattern(inner)?;
                let expr_solution = self.translate_bool_expression(expr, &inner_solution)?;
                self.translate_filter(&expr_solution, &inner_solution)
            }
            GraphPattern::Union {left, right} => {
                let left_solution = self.translate_pattern(left)?;
                let right_solution = self.translate_pattern(right)?;
                self.translate_union(&left_solution, &right_solution)
            }
            GraphPattern::Extend{inner, variable, expression} => {
                let inner_solution = self.translate_pattern(inner)?;
                let expr_solution = self.translate_expression(expression, &inner_solution)?;
                self.translate_extend(&inner_solution, variable, &expr_solution)
            }
            GraphPattern::Minus {left, right} => {
                let left_solution = self.translate_pattern(left)?;
                let right_solution = self.translate_pattern(right)?;
                nemo_def!(minus(??both, ??left) :- left_solution(??both, ??left), ~right_solution(??both, ??right); SolutionSet);
                Ok(minus)
            }
            GraphPattern::Values {variables, bindings} => {
                Ok(self.translate_values(variables, bindings))
            }
            GraphPattern::OrderBy {inner, expression: _} => {
                // SolutionSet does not contain ordering information
                let inner_solution = self.translate_pattern(inner)?;
                nemo_def!(irrelevant_order_by(??vars) :- inner_solution(??vars); SolutionSet);
                Ok(irrelevant_order_by)
            }
            GraphPattern::Project {inner, variables} => {
                let inner_solution = self.translate_pattern(inner)?;
                self.translate_project_g(&inner_solution, variables)
            }
            GraphPattern::Distinct {inner} => {
                // solution sets are always distinct
                self.translate_pattern(inner)
            }
            GraphPattern::Reduced {inner} => {
                self.translate_pattern(inner)
            }
            GraphPattern::Slice {inner, start, length} => {
                let inner_solution = self.translate_pattern(inner)?;
                Ok(self.translate_slice(&inner_solution, *start, *length))
            }
            GraphPattern::Group {inner, variables, aggregates} => {
                let inner_solution = self.translate_pattern(inner)?;
                self.translate_group_by(&inner_solution, variables, aggregates)
            }
            //GraphPattern::Service {name, inner, silent} => Err(PatternNotImplemented(pattern.clone())),
            _ => Err(PatternNotImplemented(pattern.clone()))
        }
    }

    fn translate_pattern_multi(&mut self, pattern: &GraphPattern) -> Result<SolutionMultiSet, TranslateError> {
        match pattern {
            GraphPattern::Bgp{patterns} => self.translate_bgp_multi(patterns),
            /*GraphPattern::Path {subject, path, object} =>
                Ok(SolutionMapping::from(
                    translate_path(
                        state,
                        Some(translate_node(subject)?),
                        path,
                        Some(translate_node(object)?)
                    )?
                )),*/
            //GraphPattern::Join {left, right} => translate_join_multi(state, left, right),
            //GraphPattern::LeftJoin {left, right, expression} => translate_left_join_multi(state, left, right, expression),
            //GraphPattern::Filter {expr, inner} => translate_filter_multi(state, expr, inner),
            //GraphPattern::Union {left, right} => translate_union_multi(state, left, right),
            //GraphPattern::Extend {inner, variable, expression} => translate_extend_multi(state, inner, variable, expression),
            //GraphPattern::Minus {left, right} => translate_minus_multi(state, left, right),
            //GraphPattern::Values {variables, bindings} => translate_values_multi(state, variables, bindings),
            //GraphPattern::OrderBy {inner, expression: _} => translate_order_by_multi(state, inner),
            GraphPattern::Project{inner, variables} => {
                let inner_solution = self.translate_pattern_multi(inner)?;
                self.translate_project_g(&inner_solution, variables)
            },
            GraphPattern::Distinct {inner} => {
                let inner_solution = self.translate_pattern(inner)?;
                Ok(self.get_multi(&inner_solution))
            },
            GraphPattern::Reduced {inner} => {
                let inner_solution = self.translate_pattern(inner)?;
                Ok(self.get_multi(&inner_solution))
            },
            GraphPattern::Slice {inner, start, length} => {
                let inner_solution = self.translate_pattern_seq(inner)?;
                let seq_solution = self.translate_slice_seq(&inner_solution, *start, *length);
                Ok(self.get_multi_from_sequence(&seq_solution))
            },
            //GraphPattern::Group {inner, variables, aggregates} => translate_group_by_multi(state, inner, variables, aggregates),
            //GraphPattern::Service {name, inner, silent} => Err(PatternNotImplemented(pattern.clone())),
            _ => Err(MultiPatternNotImplemented(pattern.clone()))
        }
    }

    fn translate_pattern_seq(&mut self, pattern: &GraphPattern) -> Result<SolutionSequence, TranslateError> {
        match pattern {
            GraphPattern::Distinct{inner} | GraphPattern::Reduced {inner} => {
                let inner_solution = self.translate_pattern(inner)?;
                Ok(self.get_sequence(&inner_solution))
            },
            //GraphPattern::Filter {expr, inner} => {},
            //GraphPattern::Union {left, right} => {},
            //GraphPattern::Extend {inner, variable, expression} => {},
            //Minus
            //Values
            GraphPattern::OrderBy {inner, expression} => {
                let inner_solution = self.translate_pattern_seq(inner)?;
                self.translate_order_by_seq(&inner_solution, expression)
            },
            GraphPattern::Project {inner, variables} => {
                let inner_solution = self.translate_pattern_seq(inner)?;
                self.translate_project_g(&inner_solution, variables)
            },
            GraphPattern::Slice {inner, start, length} => {
                let inner_solution = self.translate_pattern_seq(inner)?;
                Ok(self.translate_slice_seq(&inner_solution, *start, *length))
            },
            //service

            GraphPattern::Bgp {patterns: _}
            | GraphPattern::Path {subject: _, path: _, object: _}
            | GraphPattern::Join {left: _, right: _}
            | GraphPattern::LeftJoin {left: _, right: _, expression: _}
            | GraphPattern::Group {aggregates: _, variables: _, inner: _}
            => {
                let inner_solution = self.translate_pattern_multi(pattern)?;
                Ok(self.get_sequence_from_multi(&inner_solution))
            },
            _ => Err(SequencePatternNotImplemented(pattern.clone()))
        }
    }

    fn translate_describe(&mut self, pattern: &GraphPattern) -> Result<SolutionSet, TranslateError> {
        let solution = self.translate_pattern(pattern)?;
        let output_graph = SolutionSet::create("output_graph", vec![VarPtr::new("s"), VarPtr::new("s"), VarPtr::new("o")]);
        let input_graph = self.triple_set();
        for v in get_vars(&solution){
            nemo_add!(output_graph(v, ?p, ?o) :- input_graph(v, ?p, ?o), {&solution});
        }
        Ok(output_graph)
    }

    fn translate_ask(&mut self, pattern: &GraphPattern) -> Result<SolutionSet, TranslateError> {
        let solution = self.translate_pattern(pattern)?;
        let dummy = SolutionSet::create("dummy", vec![VarPtr::new("d")]);
        nemo_add!(dummy(0));
        nemo_def!(ask(true) :- {&solution}; SolutionSet);
        nemo_add!(ask(false) :- dummy(0), ~{&solution});
        Ok(ask)
    }

    fn extract_bnodes(&mut self, pattern: &TriplePattern, bnodes: &mut Vec<VarPtr>) -> Result<(), TranslateError> {
        let TriplePattern{subject, predicate: _, object} = pattern;
        self.translate_term(subject, &mut vec![], bnodes)?;
        self.translate_term(object, &mut vec![], bnodes)?;
        Ok(())
    }

    /// notes
    /// - Check if literal literals result in error in construct query subject
    /// - handle unbound variables in construct query (triples that contain them are filtered)
    /// - no graphs for construct
    /// - does construct construct constant triples also if there are no solutions?
    fn translate_construct(&mut self, pattern: &GraphPattern, template: &Vec<TriplePattern>) -> Result<SolutionSet, TranslateError> {
        let (s, p, o) = (VarPtr::new("s"), VarPtr::new("p"), VarPtr::new("o"));
        let solution = self.translate_pattern(pattern)?;
        let mut bnodes = Vec::new();
        for pattern in template {self.extract_bnodes(pattern, &mut bnodes)?}
        let bnodes = hash_dedup(&bnodes);
        let bnode_solution = SolutionSet::create("bnode_solution", nemo_terms![get_vars(&solution), &bnodes].vars());
        add_rule(&bnode_solution, Rule::new(
            get_vars(&solution).iter()
                .map(Binding::from)
                .chain(
                    bnodes.iter().map(|n| Binding::Existential(n.clone()))
                ).collect(),
            vec![to_bound_predicate(&solution)],
            vec![])
        );
        let proto_graph = SolutionSet::create("proto_graph", vec![s.clone(), p.clone(), o.clone()]);

        for t in template {
            nemo_add!(
                proto_graph(
                    self.translate_term(&t.subject, &mut vec![], &mut vec![])?,
                    match &t.predicate {
                        NamedNodePattern::NamedNode(n) => Binding::from(n),
                        NamedNodePattern::Variable(v) => Binding::from(self.sparql_vars.get(v)),
                    },
                    self.translate_term(&t.object, &mut vec![], &mut vec![])?
                ) :- {&bnode_solution}
            );
        }

        let subject_is_valid = nemo_call!(OR; nemo_call!(isNull; s), nemo_call!(isIri; s));
        let predicate_is_valid = nemo_call!(isIri; p);
        nemo_def!(construct(s, p, o) :- proto_graph(s, p, o), {nemo_filter!("", nemo_call!(AND; subject_is_valid, predicate_is_valid), " = ", true, "")}; SolutionSet);
        Ok(construct)
    }

    fn is_distinct(pattern: &GraphPattern) -> bool {
        match pattern {
            GraphPattern::Distinct {inner: _} => true,
            _ => false,
        }
    }

    /// notes
    /// - handle from (dataset) and base_iri
    /// - ASK, CONSTRUCT and DESCRIBE can use distinct always
    /// - Check that limit + order by works for construct and describe
    fn translate_query(&mut self, query: &Query) -> Result<Box<dyn TypedPredicate>, TranslateError> {
        match query {
            Query::Select {
                pattern: GraphPattern::Distinct { inner },
                dataset: _,
                base_iri: _
            } => Ok(Box::new(self.translate_pattern(inner)?)),
            Query::Select {
                pattern: GraphPattern::Slice { inner, start, length },
                dataset: _,
                base_iri: _
            } if Self::is_distinct(inner) => {
                let inner_sequence = self.translate_pattern(inner)?;
                Ok(Box::new(self.translate_slice(&inner_sequence, *start, *length)))
            }
            Query::Select {pattern, dataset: _, base_iri: _} => Ok(Box::new(self.translate_pattern_seq(pattern)?)),
            Query::Describe {pattern, dataset: _, base_iri: _} => Ok(Box::new(self.translate_describe(pattern)?)),
            Query::Ask {pattern, dataset: _, base_iri: _} => Ok(Box::new(self.translate_ask(pattern)?)),
            Query::Construct {pattern, dataset: _, base_iri: _, template} => Ok(Box::new(self.translate_construct(pattern, template)?)),
        }
    }
}

pub fn translate(query_str: &str) -> Result<String, TranslateError> {
    let query = Query::parse(query_str, None)?;
    let input_graph = PredicatePtr::new("input_graph", vec![VarPtr::new("s"), VarPtr::new("p"), VarPtr::new("o")]);
    let mut translator = QueryTranslator::new(input_graph);
    let solution_predicate = translator.translate_query(&query)?;
    Ok(construct_program(solution_predicate.as_ref()))
}
