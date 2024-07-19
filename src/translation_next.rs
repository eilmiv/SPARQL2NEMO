use std::collections::HashMap;
use std::fmt::Debug;
use spargebra::algebra::{Expression, Function, GraphPattern};
use spargebra::Query;
use spargebra::term::{BlankNode, Literal, NamedNode, NamedNodePattern, TermPattern, TriplePattern, Variable};
use crate::error::TranslateError;
use crate::error::TranslateError::{ExpressionNotImplemented, PatternNotImplemented, TermNotImplemented, Todo};
use crate::nemo_model::{add_rule, Binding, BoundPredicate, Call, construct_program, get_vars, hash_dedup, nemo_add, nemo_call, nemo_declare, nemo_def, nemo_filter, nemo_predicate_type, nemo_var, PredicatePtr, ProtoPredicate, Rule, SpecialPredicate, to_bound_predicate, TypedPredicate, VarPtr};

nemo_predicate_type!(SolutionSet = ...);
nemo_predicate_type!(SolutionMutliSet = count ...);
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
            .or_insert_with(|| VarPtr::new(&format!("?BNODE_VARIABLE_{id}")))
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

    fn translate_expression_variable(&mut self, var: &Variable, binding: &dyn TypedPredicate) -> Result<SolutionExpression, TranslateError> {
        let var_binding = self.sparql_vars.get(var);
        nemo_def!(var(var_binding; @result: var_binding) :- binding(??set_contains_var); SolutionExpression);
        Ok(var)
    }

    fn translate_expression_named_node(&mut self, node: &NamedNode) -> Result<SolutionExpression, TranslateError> {
        let named_node = SolutionExpression::create("named_node", vec![]);
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
        // create solution
        let variables: Vec<VarPtr> = inner.depend_vars().into_iter()
            .chain(list.iter().flat_map(|solution| solution.depend_vars()))
            .chain(vec![VarPtr::new("result")])
            .collect();
        let in_expression = SolutionExpression::create("in_expression", hash_dedup(&variables));

        // head
        let mut head_bindings: Vec<Binding> = get_vars(&in_expression).iter().map(Binding::from).collect();
        head_bindings.pop();
        head_bindings.push(Binding::from(false));

        // body
        let mut body = vec![to_bound_predicate(binding), to_bound_predicate(inner)];
        let mut filters = Vec::new();
        for expr in list {
            body.push(to_bound_predicate(expr));
            filters.push(SpecialPredicate::new(
                "".to_string(), vec![
                    (Binding::from(expr.result_var()), " != ".to_string()),
                    (Binding::from(inner.result_var()), "".to_string())
                ]
            ));
        }

        add_rule(&in_expression, Rule::new(head_bindings, body, filters));

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
        variables = hash_dedup(&variables);
        let result = SolutionSet::create("bgp", variables.iter().map(|v| v.clone()).collect());
        add_rule(
            &result,
            Rule::new(variables.into_iter().map(Binding::from).collect(), body_parts, vec![])
        );
        Ok(result)
    }

    fn translate_filter(&mut self, expression: &SolutionExpression, inner: &SolutionSet) -> Result<SolutionSet, TranslateError> {
        nemo_def!(filter(??expr_vars, ??other_vars) :- inner(??expr_vars, ??other_vars), expression(??expr_vars; @result: true); SolutionSet);
        Ok(filter)
    }

    fn translate_extend(&mut self, inner: &SolutionSet, var: &Variable, expression: &SolutionExpression) -> Result<SolutionSet, TranslateError> {
        let bound_var = self.sparql_vars.get(var);
        nemo_def!(extend(??e_vars, ??base_vars, bound_var) :- inner(??e_vars, ??base_vars), expression(??e_vars; @result: bound_var); SolutionSet);
        nemo_add!(extend(??vars, nemo_var!(!unbound)) :- inner(??vars));
        Ok(extend)
    }

    fn translate_project(&mut self, inner: &SolutionSet, variables: &Vec<Variable>) -> Result<SolutionSet, TranslateError> {
        let nemo_vars: Vec<VarPtr> = variables.into_iter().map(|v| self.sparql_vars.get(v)).collect();
        let projection = SolutionSet::create("projection", nemo_vars);
        nemo_add!(projection(??projected) :- inner(??projected, ??other));
        Ok(projection)
    }

    fn translate_slice(&mut self, inner: &SolutionSequence, start: usize, length: Option<usize>) -> Result<SolutionSet, TranslateError> {
        Err(Todo("implement slice"))
    }

    fn translate_pattern(&mut self, pattern: &GraphPattern) -> Result<SolutionSet, TranslateError> {
        match pattern {
            GraphPattern::Bgp {patterns} => self.translate_bgp(patterns),
            //path
            //join
            //positive exists left join
            //left join
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
            //union
            GraphPattern::Extend{inner, variable, expression} => {
                let inner_solution = self.translate_pattern(inner)?;
                let expr_solution = self.translate_expression(expression, &inner_solution)?;
                self.translate_extend(&inner_solution, variable, &expr_solution)
            }
            //minus
            //values
            //order by
            GraphPattern::Project {inner, variables} => {
                let inner_solution = self.translate_pattern(inner)?;
                self.translate_project(&inner_solution, variables)
            }
            //distinct
            //reduced
            //slice
            //group
            //GraphPattern::Service {name, inner, silent} => Err(PatternNotImplemented(pattern.clone())),
            _ => Err(PatternNotImplemented(pattern.clone()))
        }
    }

    fn translate_pattern_seq(&mut self, pattern: &GraphPattern) -> Result<SolutionSequence, TranslateError> {
        Err(Todo("implement pattern seq"))
    }

    fn translate_describe(&mut self, pattern: &GraphPattern) -> Result<SolutionSet, TranslateError> {
        Err(Todo("implement describe"))
    }

    fn translate_ask(&mut self, pattern: &GraphPattern) -> Result<SolutionSet, TranslateError> {
        Err(Todo("implement ask"))
    }

    fn translate_construct(&mut self, pattern: &GraphPattern, template: &Vec<TriplePattern>) -> Result<SolutionSet, TranslateError> {
        Err(Todo("implement construct"))
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
            } if QueryTranslator::is_distinct(inner) => {
                let inner_sequence = self.translate_pattern_seq(inner)?;
                Ok(Box::new(self.translate_slice(&inner_sequence, *start, *length)?))
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