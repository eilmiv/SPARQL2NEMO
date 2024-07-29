use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use spargebra::algebra::{AggregateExpression, Expression, Function, GraphPattern, OrderExpression, PropertyPathExpression};
use spargebra::Query;
use spargebra::term::{BlankNode, GroundTerm, Literal, NamedNode, NamedNodePattern, TermPattern, TriplePattern, Variable};
use crate::error::TranslateError;
use crate::error::TranslateError::{AggregationNotImplemented, ExpressionNotImplemented, MultiPatternNotImplemented, PathNotImplemented, PatternNotImplemented, SequencePatternNotImplemented, TermNotImplemented, Todo};
use crate::nemo_model::{add_fact, add_rule, Binding, BoundPredicate, Call, construct_program, Fact, get_vars, hash_dedup, nemo_add, nemo_atoms, nemo_call, nemo_condition, nemo_declare, nemo_def, nemo_filter, nemo_predicate_type, nemo_terms, nemo_var, PredicatePtr, ProtoPredicate, Rule, SpecialPredicate, to_bound_predicate, TypedPredicate, VarPtr};

nemo_predicate_type!(SolutionSet = ...);
nemo_predicate_type!(SolutionMultiSet = count ...);
nemo_predicate_type!(SolutionSequence = index ...);
nemo_predicate_type!(SolutionExpression = ... result);

impl SolutionExpression {
    fn depend_vars(&self) -> Vec<VarPtr> {
        let vars = self.get_predicate().vars();
        vars[..vars.len() - 1].iter().map(|v| v.clone()).collect()
    }

    fn result_var(&self) -> VarPtr {
        let vars = self.get_predicate().vars();
        vars.last().expect("expression needs to have result").clone()
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
}

impl QueryTranslator {
    fn new(input_graph: PredicatePtr) -> QueryTranslator {
        QueryTranslator{sparql_vars: VariableTranslator::new(), input_graph}
    }

    fn triple_set(&self) -> SolutionSet {
        SolutionSet::from_predicate(&self.input_graph)
    }

    fn translate_var_func(&mut self) -> impl FnMut(&Variable) -> VarPtr + '_ {
        let mut self_ref = self;
        move |var: &Variable| self_ref.sparql_vars.get(var)
    }

    fn translate_expression_variable(&mut self, var: &Variable, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let var_binding = self.sparql_vars.get(var);
        nemo_def!(var(var_binding; @result: var_binding) :- binding(??set_contains_var); SolutionExpression);
        Ok(var)
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

    fn translate_binary_function(&mut self, func: &str, left: &SolutionExpression, right: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let l = nemo_var!(l);
        let r = nemo_var!(r);
        let call = Call::new(func, vec![l.clone(), r.clone()]);
        nemo_def!(
            binary_func(??vars, ??left_vars, ??right_vars; @result: call) :-
                binding(??vars, ??left_vars, ??right_vars, ??other_vars),
                left(??vars, ??left_vars; @result: l),
                right(??vars, ??right_vars; @result: r)
            ; SolutionExpression
        );
        Ok(binary_func)
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

    fn translate_exists(&mut self, pattern_solution: &SolutionSet, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let partial_exists = self.translate_positive_exists(pattern_solution, binding)?;
        nemo_def!(exists(??vars; @result: true) :- partial_exists(??vars; @result: true); SolutionExpression);
        nemo_add!(exists(??vars; @result: false) :- binding(??vars, ??other), ~partial_exists(??vars; @result: true));
        Ok(exists)
    }

    fn translate_if(&mut self, condition: &SolutionExpression, true_val: &SolutionExpression, false_val: &SolutionExpression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let vars: Vec<VarPtr> = condition.depend_vars().into_iter()
            .chain(true_val.depend_vars().into_iter())
            .chain(false_val.depend_vars().into_iter())
            .chain(vec![VarPtr::new("result")])
            .collect();

        let if_expression = SolutionExpression::create("if_expression", hash_dedup(&vars));
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

    fn translate_effective_boolean_value(&mut self, expression: &SolutionExpression) -> Result<SolutionExpression, TranslateError> {
        // bools
        nemo_def!(effective_boolean_value(??vars; @result: false) :- expression(??vars; @result: ?v), {nemo_filter!("", ?v, " = ", false, "")}; SolutionExpression);
        nemo_def!(effective_boolean_value(??vars; @result: true) :- expression(??vars; @result: ?v), {nemo_filter!("", ?v, " = ", true, "")}; SolutionExpression);

        // strings
        nemo_add!(effective_boolean_value(??vars; @result: false) :- expression(??vars; @result: ?v), {nemo_filter!("STRLEN(", ?v, ") = 0")});
        nemo_add!(effective_boolean_value(??vars; @result: true) :- expression(??vars; @result: ?v), {nemo_filter!("STRLEN(", ?v, ") > 0")});

        // numbers
        nemo_add!(effective_boolean_value(??vars; @result: false) :- expression(??vars; @result: ?v), {nemo_filter!("", ?v, " = 0")});
        nemo_add!(effective_boolean_value(??vars; @result: true) :- expression(??vars; @result: ?v), {nemo_filter!("", ?v, " != 0")}, {nemo_filter!("isNumeric(", ?v, ") = ", true, "")});

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
            Expression::In(_, _) | Expression::Exists(_) |
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
        let call = Call::new(func, expressions.iter().map(|e| e.result_var()).map(Binding::from).collect());
        let vars: Vec<VarPtr> = hash_dedup(&expressions.iter().flat_map(|e| e.depend_vars()).collect());
        let solution_vars: Vec<VarPtr> = vars.iter().map(|v| v.clone()).chain(vec![VarPtr::new("result")]).collect();
        let head_bindings: Vec<Binding> = vars.iter().map(Binding::from).chain(vec![Binding::from(call)]).collect();
        let solution = SolutionExpression::create(&func.to_lowercase(), solution_vars);
        add_rule(&solution,
                 Rule::new(
                     head_bindings,
                     expressions.iter().map(|e| to_bound_predicate(e)).chain(vec![to_bound_predicate(binding)]).collect(),
                     vec![]
                 )
        );
        Ok(solution)
    }

    fn translate_function(&mut self, func: &Function, parameter_expressions: &Vec<Expression>, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let params = parameter_expressions.iter().map(|e| self.translate_expression(e, binding)).collect::<Result<Vec<_>, _>>()?;
        match func {
            Function::Str => self.function(&params, binding, "STR"),
            Function::Lang => self.function(&params, binding, "LANG"),
            // LangMatches -> language tag matches a lang range e.g. en-US, de-*
            Function::Datatype => self.function(&params, binding, "DATATYPE"),
            // Iri
            // BNode
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
            // Year
            // Month
            // Day
            // Hours
            // Minutes
            // Seconds
            // Timezone -> timezone as dayTimeDuration
            // Tz -> timezone as simple literal
            // Now
            // Uuid
            // StrUuid
            // Md5
            // Sha1
            // Sha256
            // Sha384
            // Sha512
            // StrLang -> constructs lang string
            // StrDt -> constructs literal with datatype
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
            // Triple
            // Subject
            // Predicate
            // Object
            // IsTriple
            // Adjust -> no clue what this is
            Function::Custom(func_iri) => {
                match func_iri.as_str() {
                    "http://www.w3.org/2005/xpath-functions/math#sqrt" => self.function(&params, binding, "SQRT"),
                    "http://www.w3.org/2005/xpath-functions/math#sin" => self.function(&params, binding, "SIN"),
                    "http://www.w3.org/2005/xpath-functions/math#cos" => self.function(&params, binding, "COS"),
                    "http://www.w3.org/2005/xpath-functions/math#tan" => self.function(&params, binding, "TAN"),
                    // round
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
                    _ => Err(TranslateError::FunctionNotImplemented(func.clone()))
                }
            }
            _ => Err(TranslateError::FunctionNotImplemented(func.clone()))
        }
    }

    fn translate_expression(&mut self, expression: &Expression, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        match expression {
            Expression::Variable(v) => self.translate_expression_variable(v, binding),
            Expression::NamedNode(n) => self.translate_expression_named_node(n),
            Expression::Literal(l) => self.translate_expression_literal(l),
            Expression::Or(left, right) => {
                let left_solution = self.translate_bool_expression(left, binding)?;
                let right_solution = self.translate_bool_expression(right, binding)?;
                self.translate_binary_function("OR", &left_solution, &right_solution, binding)
            },
            Expression::And(left, right) => {
                let left_solution = self.translate_bool_expression(left, binding)?;
                let right_solution = self.translate_bool_expression(right, binding)?;
                self.translate_binary_function("AND", &left_solution, &right_solution, binding)
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
                self.translate_by_cases(
                    nemo_filter!("", ?l, " > ", ?r, ""),
                    nemo_filter!("", ?l, " <= ", ?r, ""),
                    &left_solution, &right_solution, binding
                )
            },
            Expression::GreaterOrEqual(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_by_cases(
                    nemo_filter!("", ?l, " >= ", ?r, ""),
                    nemo_filter!("", ?l, " < ", ?r, ""),
                    &left_solution, &right_solution, binding
                )
            },
            Expression::Less(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_by_cases(
                    nemo_filter!("", ?l, " < ", ?r, ""),
                    nemo_filter!("", ?l, " >= ", ?r, ""),
                    &left_solution, &right_solution, binding
                )
            },
            Expression::LessOrEqual(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_by_cases(
                    nemo_filter!("", ?l, " <= ", ?r, ""),
                    nemo_filter!("", ?l, " > ", ?r, ""),
                    &left_solution, &right_solution, binding
                )
            },
            Expression::Equal(left, right) => {
                let left_solution = self.translate_expression(left, binding)?;
                let right_solution = self.translate_expression(right, binding)?;
                self.translate_by_cases(
                    nemo_filter!("", ?l, " = ", ?r, ""),
                    nemo_filter!("", ?l, " != ", ?r, ""),
                    &left_solution, &right_solution, binding
                )
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
            }
            // bound
            Expression::If(cond, true_val, false_val) => {
                let cond_solution = self.translate_bool_expression(cond, binding)?;
                let true_solution = self.translate_expression(true_val, binding)?;
                let false_solution = self.translate_expression(false_val, binding)?;
                self.translate_if(&cond_solution, &true_solution, &false_solution, binding)
            }
            // coalesce
            Expression::FunctionCall(func, params) => self.translate_function(func, params, binding),
            _ => Err(ExpressionNotImplemented(expression.clone()))
        }
    }


    fn translate_term(&mut self, term: &TermPattern, variables: &mut Vec<VarPtr>, bnode_vars: &mut Vec<VarPtr>) -> Result<Binding, TranslateError> {
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
            }
            _ => return Err(TermNotImplemented(term.clone()))
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

    fn translate_bgp(&mut self, patterns: &Vec<TriplePattern>) -> Result<SolutionSet, TranslateError> {
        let mut variables = Vec::new();
        let mut body_parts = Vec::new();
        for triple in patterns {
            body_parts.push(self.translate_triple(triple, &mut variables, &mut vec![])?)
        }
        if patterns.is_empty() {
            let dummy = SolutionSet::create("dummy",vec![]);
            nemo_add!(dummy());
            body_parts.push(to_bound_predicate(&dummy))
        }
        variables = hash_dedup(&variables);
        let result = SolutionSet::create("bgp", variables.iter().map(|v| v.clone()).collect());
        add_rule(
            &result,
            Rule::new(variables.into_iter().map(Binding::from).collect(), body_parts, vec![])
        );
        Ok(result)
    }

    fn translate_bgp_multi(&mut self, patterns: &Vec<TriplePattern>) -> Result<SolutionMultiSet, TranslateError> {
        let mut variables = Vec::new();
        let mut bnode_vars = Vec::new();
        let mut body_parts = Vec::new();
        for triple in patterns {
            body_parts.push(self.translate_triple(triple, &mut variables, &mut bnode_vars)?)
        }
        variables = hash_dedup(&variables);
        variables.insert(0, VarPtr::new("count"));
        bnode_vars = hash_dedup(&bnode_vars);
        let result = SolutionMultiSet::create("bgp", variables.iter().map(|v| v.clone()).collect());
        let mut bindings: Vec<_> = variables.into_iter().map(Binding::from).collect();
        bindings[0] = if bnode_vars.is_empty() {
            Binding::from(1)
        } else {
            Binding::Call(Call::new("#count", bnode_vars.iter().map(Binding::from).collect()))
        };
        add_rule(
            &result,
            Rule::new(bindings, body_parts, vec![])
        );
        Ok(result)
    }

    fn is_constant(b: &Binding) -> bool {
        match b {
            Binding::Constant(c) => true,
            Binding::Variable(v) => false,
            _ => panic!("this function should only be called with variables or constants")
        }
    }

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

    fn zero_path_extend(&mut self, start: Binding, path: SolutionSet, end: Binding) -> SolutionSet {
        // start and end are different constants -> there is no zero path
        if Self::is_constant(&start) && Self::is_constant(&end) && &start != &end { return path }
        //if let Binding::Constant(c1) = start { if let Binding::Constant(c2) = end { if c1 != c2 { return path } } }

        let start_constant = if Self::is_constant(&start) {Some(start)} else {None};
        let end_constant = if Self::is_constant(&end) {Some(end)} else {None};
        let constant = start_constant.or(end_constant);

        if let Some(c) = constant {
            // one term (the other one is a variable) or two terms (start and end are the same)
            nemo_add!(path(c, c));
            path
        }
        else {
            // no constants
            let input_graph = self.triple_set();
            nemo_add!(path(?s, ?s) :- input_graph(?s, ?p, ?o));
            nemo_add!(path(?o, ?o) :- input_graph(?s, ?p, ?o));
            path
        }
    }

    fn translate_negated_property_set(&mut self, start: Binding, properties: &Vec<NamedNode>, end: Binding) -> SolutionSet {
        let property_var = nemo_var!(property_var);
        let filters = properties.iter().enumerate().flat_map(
            |(i, p)| [
                (property_var.clone(), " != ".to_string()),
                (Binding::from(p), if i == properties.len() - 1 {"".to_string()} else {", ".to_string()})
            ]
        ).collect();
        let filter = SpecialPredicate::new("".to_string(), filters);
        let graph = self.triple_set();
        nemo_def!(negated_property_set(start, end) :- graph(start, property_var, end), {filter}; SolutionSet);
        negated_property_set
    }

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
            _ => Err(TranslateError::PathNotImplemented(path.clone()))
        }
    }

    fn translate_left_join(&mut self, left: &Box<GraphPattern>, right: &Box<GraphPattern>, expression: &Option<Expression>) -> Result<SolutionSet, TranslateError> {
        let left_solution = self.translate_pattern(left)?;
        let right_solution = self.translate_pattern(right)?;
        nemo_def!(raw_join(??both, ??left, ??right) :- left_solution(??both, ??left), right_solution(??both, ??right); SolutionSet);
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
        nemo_def!(left_join(??vars) :- filtered_join(??vars); SolutionSet);
        add_rule(&left_join, Rule::new(get_vars(&left_join).iter().map(
            |v| if get_vars(&left_solution).contains(v) { Binding::from(v) } else { Binding::Existential(v.clone()) }
        ).collect(), vec![to_bound_predicate(&left_solution)], vec![]));

        Ok(left_join)
    }

    fn translate_filter(&mut self, expression: &SolutionExpression, inner: &SolutionSet) -> Result<SolutionSet, TranslateError> {
        nemo_def!(filter(??expr_vars, ??other_vars) :- inner(??expr_vars, ??other_vars), expression(??expr_vars; @result: true); SolutionSet);
        Ok(filter)
    }

    fn translate_union(&mut self, left: &SolutionSet, right: &SolutionSet) -> Result<SolutionSet, TranslateError> {
        let left_vars = get_vars(left);
        let right_vars = get_vars(right);
        let all_vars = hash_dedup(&left_vars.iter().chain(&right_vars).map(|v| v.clone()).collect());
        let union = SolutionSet::create("union", all_vars.iter().map(|v| v.clone()).collect());
        let left_bindings = all_vars.iter().map(
            |v| if left_vars.contains(v) {Binding::from(v)} else {Binding::Existential(v.clone())}
        ).collect();
        let right_bindings = all_vars.iter().map(
            |v| if right_vars.contains(v) {Binding::from(v)} else {Binding::Existential(v.clone())}
        ).collect();
        add_rule(&union, Rule::new(left_bindings, vec![to_bound_predicate(left)], vec![]));
        add_rule(&union, Rule::new(right_bindings, vec![to_bound_predicate(right)], vec![]));
        Ok(union)
    }

    fn translate_extend(&mut self, inner: &SolutionSet, var: &Variable, expression: &SolutionExpression) -> Result<SolutionSet, TranslateError> {
        let bound_var = self.sparql_vars.get(var);
        nemo_def!(extend(??e_vars, ??base_vars, bound_var) :- inner(??e_vars, ??base_vars), expression(??e_vars; @result: bound_var); SolutionSet);
        nemo_add!(extend(??vars, nemo_var!(!unbound)) :- inner(??vars));
        Ok(extend)
    }

    fn translate_ground_term(&mut self, term: &Option<GroundTerm>) -> Binding {
        match term {
            None => nemo_var!(!UNDEF),
            Some(GroundTerm::Literal(l)) => Binding::from(l),
            Some(GroundTerm::NamedNode(n)) => Binding::from(n),
            _ => unreachable!("rdf* feature is not enabled")
        }
    }

    fn translate_values(&mut self, variables: &Vec<Variable>, bindings: &Vec<Vec<Option<GroundTerm>>>) -> SolutionSet {
        let dummy = SolutionSet::create("dummy", vec![VarPtr::new("x")]);
        let values = SolutionSet::create("values", variables.iter().map(|v| self.sparql_vars.get(v)).collect());
        nemo_add!(dummy(1));
        for binding in bindings {
            add_rule(&values, Rule::new(binding.iter().map(|b| self.translate_ground_term(b)).collect(), vec![to_bound_predicate(&dummy)], vec![]))
        }
        values
    }

    fn translate_project(&mut self, inner: &SolutionSet, variables: &Vec<Variable>) -> Result<SolutionSet, TranslateError> {
        let nemo_vars: Vec<VarPtr> = variables.into_iter().map(|v| self.sparql_vars.get(v)).collect();
        let projection = SolutionSet::create("projection", nemo_vars);
        nemo_add!(projection(??projected) :- inner(??projected, ??other));
        Ok(projection)
    }

    fn translate_project_multi(&mut self, inner: &SolutionMultiSet, variables: &Vec<Variable>) -> Result<SolutionMultiSet, TranslateError> {
        let mut nemo_vars: Vec<VarPtr> = variables.into_iter().map(|v| self.sparql_vars.get(v)).collect();
        nemo_vars.insert(0, VarPtr::new("count"));
        let projection = SolutionMultiSet::create("projection", nemo_vars);
        nemo_add!(projection(@count: ?c; ??projected) :- inner(@count: ?c; ??projected, ??other));
        Ok(projection)
    }

    fn translate_project_seq(&mut self, inner: &SolutionSequence, variables: &Vec<Variable>) -> Result<SolutionSequence, TranslateError> {
        let mut nemo_vars: Vec<VarPtr> = variables.into_iter().map(|v| self.sparql_vars.get(v)).collect();
        nemo_vars.insert(0, VarPtr::new("index"));
        let projection = SolutionSequence::create("projection", nemo_vars);
        nemo_add!(projection(@index: ?i; ??projected) :- inner(@index: ?i; ??projected, ??other));
        Ok(projection)
    }

    fn translate_slice_seq(&mut self, inner: &SolutionSequence, start: usize, length: Option<usize>) -> SolutionSequence {
        let index = nemo_var!(index);
        let lower = nemo_filter!("", index, " >= ", start, "");
        let upper = match length {
            None => nemo_filter!("0 = 0"),
            Some(l) => nemo_filter!("", index, " < ", start + l, ""),
        };
        nemo_def!(slice(@index: index.clone() - start; ??vars) :- inner(@index: index; ??vars), {lower}, {upper}; SolutionSequence);
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
            vec![expr_solution.result_var()]
        }
        else {
            vec![expr_solution.result_var()].iter()
                .chain(get_vars(inner).iter().filter(|v| !group_vars.contains(v)))
                .map(|v| v.clone())
                .collect()
        };
        let aggregate = SolutionSet::create(&format!("{aggregation}_aggregate"), group_vars.iter().map(|v| v.clone()).chain(vec![variable]).collect());
        let aggregation_call = Call::new(&format!("#{aggregation}"), aggregate_vars.iter().map(Binding::from).collect());
        nemo_add!(aggregate(??group_vars, aggregation_call) :- inner(??group_vars, ??other), {&expr_solution});
        Ok(aggregate)
    }

    fn translate_count_all(&mut self, inner: &dyn TypedPredicate, variable: VarPtr, group_vars: Vec<VarPtr>) -> Result<SolutionSet, TranslateError> {
        let aggregate_vars: Vec<VarPtr> = get_vars(inner).iter().filter(|v| !group_vars.contains(v)).map(|v| v.clone()).collect();
        let aggregation_call = Call::new("#count", aggregate_vars.iter().map(Binding::from).collect());
        let count_all = SolutionSet::create("count_all", group_vars.into_iter().chain(vec![variable]).collect());
        nemo_add!(count_all(??group_vars, aggregation_call) :- inner(??group_vars, ??other));
        Ok(count_all)
    }

    fn translate_group_by(&mut self, inner: &SolutionSet, group_vars: &Vec<Variable>, aggregates: &Vec<(Variable, AggregateExpression)>) -> Result<SolutionSet, TranslateError> {
        let collect_aggregations = SolutionSet::create(
            "collect_aggregations",
            group_vars.iter().chain(aggregates.iter().map(|(v, a)| v)).map(|v| self.sparql_vars.get(v)).collect()
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
    fn translate_sort(&mut self, inner: &SolutionSequence, order_expression: &OrderExpression) -> Result<SolutionSequence, TranslateError> {
        let val = nemo_var!(sort_val);
        let other_val = nemo_var!(other_sort_val);
        let index = nemo_var!(index);
        let other_index = nemo_var!(other_index);
        let (filter, expression) = match order_expression {
            OrderExpression::Asc(e) => (nemo_filter!("", other_val, " <= ", val, ""), e),
            OrderExpression::Desc(e) => (nemo_filter!("", other_val, " >= ", val, ""), e),
        };

        let expression_solution = self.translate_expression(expression, inner)?;
        nemo_def!(sort_condition(?i, ??both, ??depend; @result: ?r) :- inner(@index: ?i; ??both, ??depend), expression_solution(??depend; @result: ?r); SolutionExpression);
        nemo_def!(sorted_proto(@index: %count(other_index); ??vars) :- sort_condition(?i, ??vars; @result: val), sort_condition(other_index, ??*other_vars; @result: other_val), {filter}; SolutionSequence);

        let index_filter = nemo_filter!("", other_index, " >= ", index, "");
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
                nemo_def!(join(??both, ??left, ??right) :- left_solution(??both, ??left), right_solution(??both, ??right); SolutionSet);
                Ok(join)
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
            GraphPattern::OrderBy {inner, expression} => {
                // SolutionSet does not contain ordering information
                let inner_solution = self.translate_pattern(inner)?;
                nemo_def!(irrelevant_order_by(??vars) :- inner_solution(??vars); SolutionSet);
                Ok(irrelevant_order_by)
            }
            GraphPattern::Project {inner, variables} => {
                let inner_solution = self.translate_pattern(inner)?;
                self.translate_project(&inner_solution, variables)
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
                self.translate_project_multi(&inner_solution, variables)
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
                self.translate_project_seq(&inner_solution, variables)
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
        // return Err(PatternNotImplemented(pattern.clone()));
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
        let TriplePattern{subject, predicate, object} = pattern;
        self.translate_term(subject, &mut vec![], bnodes)?;
        self.translate_term(object, &mut vec![], bnodes)?;
        Ok(())
    }

    fn translate_construct(&mut self, pattern: &GraphPattern, template: &Vec<TriplePattern>) -> Result<SolutionSet, TranslateError> {
        let (s, p, o) = (VarPtr::new("s"), VarPtr::new("p"), VarPtr::new("o"));
        let solution = self.translate_pattern(pattern)?;
        let mut bnodes = Vec::new();
        for pattern in template {self.extract_bnodes(pattern, &mut bnodes)?}
        let bnodes = hash_dedup(&bnodes);
        let bnode_solution = SolutionSet::create("bnode_solution", get_vars(&solution).iter().chain(bnodes.iter()).map(|v| v.clone()).collect());
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