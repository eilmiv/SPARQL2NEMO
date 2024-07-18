use std::collections::HashMap;
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
                nemo_def!(
                    add(??vars, ??left, ??right; @result: l.clone() + r.clone()) :-
                        binding(??var, ??left, ??right, ??other),
                        left_solution(??vars, ??left; @result: l),
                        right_solution(??vars, ??right; @result: r)
                        ; SolutionExpression
                );
                Ok(add)
            }
            // subtract
            // multiply
            // divide
            // unary plus
            // unary minus
            // exists
            // if
            // function call
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
            //left join
            // positive exists filter
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