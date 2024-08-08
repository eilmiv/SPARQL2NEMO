use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops;
use std::rc::Rc;
use std::str::FromStr;
use spargebra::term::Term;

const TRUE: &'static str = "\"true\"^^<http://www.w3.org/2001/XMLSchema#boolean>";
const FALSE: &'static str = "\"false\"^^<http://www.w3.org/2001/XMLSchema#boolean>";

/// Variable defines meaning of position in NEMO predicate
/// Variables can be shared by multiple predicates
/// Two variables with the same label are not the same
#[derive(Debug)]
pub struct Variable {
    /// Label is used in predicate name generation
    label: String
}

impl Variable {
    fn new(label: &str) -> Variable {
        Variable{label: label.to_string()}
    }

    pub fn create(label: &str) -> VarPtr {
        VarPtr::new(label)
    }
}

macro_rules! nemo_var {
    (!$label:ident) => {
        crate::nemo_model::Binding::Existential(
            crate::nemo_model::Variable::create(stringify!($label))
        )
    };
    ($label:ident) => {
        crate::nemo_model::Binding::Variable(
            crate::nemo_model::Variable::create(stringify!($label))
        )
    };
}


macro_rules! nemo_iri {
    ($immediate_iri:ident) => {crate::nemo_model::Binding::Constant(stringify!($immediate_iri).to_string())};
    ($literal_iri:literal) => {crate::nemo_model::Binding::Constant(format!("<{}>", $literal_iri))};
    ($prefix:expr => $suffix:ident) => {crate::nemo_model::Binding::Constant(format!("<{}{}>", $prefix, stringify!($suffix)))};
    ($prefix:expr => $suffix:literal) => {crate::nemo_model::Binding::Constant(format!("<{}{}>", $prefix, $suffix))};
}

pub struct TermSet {
    variables: Vec<VarPtr>,
    binding_map: HashMap<VarPtr, Binding>
}

impl TermSet {
    pub fn new() -> Self {
        TermSet{variables: Vec::new(), binding_map: HashMap::new()}
    }

    pub fn from_bindings(bindings: &Vec<Binding>) -> Self {
        let mut term_set = Self::new();
        for v in bindings {term_set.add_binding(v)}
        term_set
    }

    pub fn add_var(&mut self, var: &VarPtr) {
        self.variables.push(var.clone())
    }

    pub fn add_binding(&mut self, binding: &Binding){
        let v = binding.variable();
        self.add_var(&v);
        self.binding_map.insert(v, binding.clone());
    }

    pub fn extend(&mut self, other: &TermSet){
        for binding in other.bindings() {
            self.add_binding(&binding);
        }
    }

    pub fn vars(&self) -> Vec<VarPtr> {
        hash_dedup(&self.variables)
    }

    pub fn bindings(&self) -> Vec<Binding> {
        self.vars().iter()
            .map(|v| self.binding_map.get(v).unwrap_or(&Binding::from(v)).clone())
            .collect()
    }
}

impl Clone for TermSet {
    fn clone(&self) -> Self {
        TermSet{
            variables: self.variables.iter().map(|v| v.clone()).collect(),
            binding_map: self.binding_map.iter().map(|(v, b)| (v.clone(), b.clone())).collect()
        }
    }
}

impl From<&TermSet> for TermSet {
    fn from(value: &TermSet) -> Self {
        value.clone()
    }
}

impl<T> From<T> for TermSet where Binding: From<T> {
    fn from(value: T) -> Self {
        TermSet::from_bindings(&vec![Binding::from(value)])
    }
}

impl<T> From<Vec<T>> for TermSet where Binding: From<T> {
    fn from(value: Vec<T>) -> Self {
        let bindings: Vec<Binding> = value.into_iter().map(Binding::from).collect();
        TermSet::from_bindings(&bindings)
    }
}

impl<T> From<&Vec<T>> for TermSet where Binding: for<'a> From<&'a T> {
    fn from(value: &Vec<T>) -> Self {
        let bindings: Vec<Binding> = value.into_iter().map(|v: &T| Binding::from(v)).collect();
        TermSet::from_bindings(&bindings)
    }
}

macro_rules! nemo_terms {
    ($($part:expr $(=> $func:expr)? ),*) => {
        {
            #[allow(unused_mut)]
            let mut term_set = crate::nemo_model::TermSet::new();
            $(
                #[allow(unused_variables)]
                let to_add = vec![$part];
                $(
                    let to_add: Vec<crate::nemo_model::TermSet> = ($part).iter().map($func).map(crate::nemo_model::TermSet::from).collect();
                )?

                for part in to_add {
                    term_set.extend(&crate::nemo_model::TermSet::from(part));
                }
            )*
            term_set
        }
    };
}

#[derive(Debug)]
pub struct VarPtr {
    ptr: Rc<Variable>
}

impl VarPtr {
    pub fn new(label: &str) -> VarPtr {
        VarPtr{ptr: Rc::new(Variable::new(label))}
    }

    pub fn label(&self) -> String {
        self.ptr.label.clone()
    }

    pub fn clone(&self) -> VarPtr {
        VarPtr{ptr: self.ptr.clone()}
    }

    pub fn distinct_new(&self) -> VarPtr {
        VarPtr::new(&self.label())
    }
}

impl Display for VarPtr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("?")?;
        f.write_str(&self.label())
    }
}

impl PartialEq for VarPtr {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.ptr, &other.ptr)
    }
}
impl Eq for VarPtr {}

impl Hash for VarPtr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let ptr: *const Variable = Rc::as_ptr(&self.ptr);
        ptr.hash(state);
    }
}

/// A position in a predicate
#[derive(Debug)]
struct PredicatePos {
    /// The associated variable
    variable: VarPtr,
    /// Flags to track properties of that position explicitly.
    /// These are only the explicit properties, there are more properties inferred in [PredicatePtr::property_at].
    properties: u32,
}

impl PredicatePos{
    pub fn new(variable: VarPtr) -> PredicatePos{
        PredicatePos{variable, properties: u32::MAX}
    }
}

#[derive(Debug)]
#[derive(Clone)]
pub struct Call {
    func: String,
    params: Vec<Binding>
}

impl Call {
    pub fn new(func: &str, params: Vec<Binding>) -> Call {
        Call{func: func.to_string(), params}
    }

    fn nemo_string(&self, var_names: &mut VariableTranslator) -> String {
        let str_vec: Vec<String> = self.params.iter().map(|p| p.nemo_string(var_names)).collect();
        format!(
            "{}({})",
            self.func,
            str_vec.join(", ")
        )
    }
}

macro_rules! nemo_call {
    ($func:ident; $($param:expr),*) => {
        crate::nemo_model::Binding::Call(
            crate::nemo_model::Call::new(
                stringify!($func), vec![
                    $(crate::nemo_model::Binding::from(&$param)),*
                ]
            )
        )
    };
}

#[derive(Debug)]
#[derive(Clone)]
pub struct Operation {
    op: String,
    left: Option<Box<Binding>>,
    right: Box<Binding>,
}

impl Operation {
    pub fn new(op: &str, left: Binding, right: Binding) -> Operation {
        Operation {op: op.to_string(), left: Some(Box::new(left)), right: Box::new(right)}
    }

    fn nemo_string(&self, var_names: &mut VariableTranslator) -> String {
        let mut format_operand = |operand: &Binding| -> String {
            match operand {
                Binding::Constant(_)
                | Binding::Existential(_)
                | Binding::Variable(_)
                | Binding::Call(_) => operand.nemo_string(var_names),
                Binding::Operation(o) => format!("({})", o.nemo_string(var_names))
            }
        };
        let mut left = "".to_string();
        if let Some(l) = &self.left {
            left = format_operand(l);
        }
        format!(
            "{left} {} {}",
            self.op,
            format_operand(&self.right)
        )
    }

    fn var_name(&self) -> &'static str {
        match self.op.as_str() {
            "+" => "SUM",
            "*" => "PRODUCT",
            _ => "OPERATION"
        }
    }
}

/// A binding of a predicate position in a [Rule]
#[derive(Debug)]
pub enum Binding {
    Constant(String),
    Variable(VarPtr),
    Existential(VarPtr),
    Call(Call),
    Operation(Operation),
}

impl Binding {
    fn nemo_string(&self, var_names: &mut VariableTranslator) -> String {
        match self {
            Binding::Constant(s) => s.clone(),
            Binding::Variable(v) => format!("?{}", var_names.get(v.clone())),
            Binding::Existential(v) => format!("!{}", var_names.get(v.clone())),
            Binding::Call(c) => c.nemo_string(var_names),
            Binding::Operation(o) => o.nemo_string(var_names),
        }
    }

    fn variable(&self) -> VarPtr {
        match self {
            Binding::Constant(_) => VarPtr::new("CONST"),
            Binding::Variable(v) => v.clone(),
            Binding::Existential(v) => v.clone(),
            Binding::Call(c) => VarPtr::new(&c.func.to_uppercase()),
            Binding::Operation(o) => VarPtr::new(o.var_name()),
        }
    }
}

impl Clone for Binding{
    fn clone(&self) -> Self {
        match self {
            Binding::Variable(v) => Binding::Variable(v.clone()),
            Binding::Existential(v) => Binding::Existential(v.clone()),
            Binding::Constant(c) => Binding::Constant(c.clone()),
            Binding::Call(c) => Binding::Call(c.clone()),
            Binding::Operation(o) => Binding::Operation(o.clone()),
        }
    }
}

impl PartialEq for Binding{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Binding::Variable(l), Binding::Variable(r)) => l == r,
            (Binding::Existential(l), Binding::Existential(r)) => l == r,
            (Binding::Constant(l), Binding::Constant(r)) => {
                let term1 = Term::from_str(l.as_str());
                let term2 = Term::from_str(r.as_str());
                match (term1, term2) {
                    (Ok(tl), Ok(tr)) => tl == tr,
                    _ => l == r
                }
            },
            (Binding::Call(Call{func, params}), Binding::Call(Call{func: r_func, params: r_params})) => {
                func == r_func && params.iter().zip(r_params).all(|(l, r)| l == r)
            }
            (Binding::Operation(Operation{op, left, right}), Binding::Operation(Operation{op: r_op, left: r_left, right: r_right})) => {
                op == r_op && left == r_left && right == r_right
            }
            _ => false
        }
    }
}

impl From<&VarPtr> for Binding {
    fn from(value: &VarPtr) -> Self {
        Binding::Variable(value.clone())
    }
}

impl From<VarPtr> for Binding {
    fn from(value: VarPtr) -> Self {
        Binding::Variable(value)
    }
}

impl From<&&str> for Binding {
    fn from(value: &&str) -> Self {
        Binding::Constant(format!("\"{}\"", value))
    }
}

impl From<&str> for Binding {
    fn from(value: &str) -> Self {
        Binding::Constant(format!("\"{}\"", value))
    }
}

impl From<&String> for Binding {
    fn from(value: &String) -> Self {
        Binding::Constant(format!("\"{}\"", value))
    }
}

impl From<String> for Binding {
    fn from(value: String) -> Self {
        Binding::Constant(format!("\"{}\"", value))
    }
}

impl From<&usize> for Binding {
    fn from(value: &usize) -> Self {
        Binding::Constant(format!("{}", value))
    }
}

impl From<usize> for Binding {
    fn from(value: usize) -> Self {
        Binding::Constant(format!("{}", value))
    }
}

impl From<&i32> for Binding {
    fn from(value: &i32) -> Self {
        Binding::Constant(format!("{}", value))
    }
}

impl From<i32> for Binding {
    fn from(value: i32) -> Self {
        Binding::Constant(format!("{}", value))
    }
}

impl From<&bool> for Binding {
    fn from(value: &bool) -> Self {
        Binding::Constant(if *value {TRUE.to_string()} else {FALSE.to_string()})
    }
}

impl From<bool> for Binding {
    fn from(value: bool) -> Self {
        Binding::Constant(if value {TRUE.to_string()} else {FALSE.to_string()})
    }
}

impl From<&f64> for Binding {
    fn from(value: &f64) -> Self {
        Binding::Constant(value.to_string())
    }
}

impl From<f64> for Binding {
    fn from(value: f64) -> Self {
        Binding::Constant(value.to_string())
    }
}

impl From<&Call> for Binding {
    fn from(value: &Call) -> Self {
        Binding::Call(value.clone())
    }
}

impl From<Call> for Binding {
    fn from(value: Call) -> Self {
        Binding::Call(value.clone())
    }
}

impl From<&Binding> for Binding {
    fn from(value: &Binding) -> Self {
        value.clone()
    }
}

macro_rules! binding_operator {
    ($class_name:ident, $func_name:ident, $op:literal) => {
        impl<T: Into<Binding>> ops::$class_name<T> for Binding where Binding: From<T> {
            type Output = Binding;

            fn $func_name(self, rhs: T) -> Self::Output {
                Binding::Operation(Operation::new($op, self, Binding::from(rhs)))
            }
        }

        impl ops::$class_name<Binding> for usize {
            type Output = Binding;

            fn $func_name(self, rhs: Binding) -> Self::Output {
                Binding::Operation(Operation::new($op, Binding::from(self), rhs))
            }
        }
    };
}

binding_operator!(Add, add, "+");
binding_operator!(Mul, mul, "*");
binding_operator!(Div, div, "/");
binding_operator!(Sub, sub, "-");


fn make_non_empty(bindings: String) -> String {
    if bindings.is_empty(){ "arity_zero".to_string() }
    else { bindings }
}


/// A predicate with bound positions
#[derive(Debug)]
pub struct BoundPredicate {
    /// The predicate to be used
    predicate: PredicatePtr,
    /// define bindings for some position of the predicate
    bindings: Vec<Binding>,
    /// whether the predicate is negated
    negated: bool
}

impl BoundPredicate {
    pub(crate) fn new(predicate: PredicatePtr, bindings: Vec<Binding>, negated: bool) -> BoundPredicate {
        BoundPredicate{predicate, bindings, negated}
    }

    fn nemo_string(&self, var_names: &mut VariableTranslator, state: &mut GenState) -> String {
        let inner = make_non_empty(self.bindings.iter()
            .map(|b| b.nemo_string(var_names))
            .collect::<Vec<_>>()
            .join(", "));
        let predicate_name = self.predicate.construct_program(state);
        let negated = if self.negated {"~"} else {""};
        format!("{negated}{predicate_name}({inner})")
    }
}

/// for filter conditions
#[derive(Debug)]
pub struct SpecialPredicate {
    bindings: Vec<(Binding, String)>,
    prefix: String
}

impl SpecialPredicate {
    pub fn new(prefix: String, bindings: Vec<(Binding, String)>) -> SpecialPredicate {
        SpecialPredicate {bindings, prefix}
    }

    fn nemo_string(&self, var_names: &mut VariableTranslator) -> String {
        let binding_strings: Vec<String> = self.bindings.iter().map(
            |(binding, suffix)|
            format!(
                "{}{suffix}",
                binding.nemo_string(var_names)
            )
        ).collect();
        format!("{}{}", self.prefix, binding_strings.join(""))
    }
}

macro_rules! nemo_filter {
    (
        $prefix:literal $(
            ,
            $(?$var:ident, $var_suffix:literal)?
            $($expr:expr, $expr_suffix:literal)?
        )*
    ) => {
        crate::nemo_model::ProtoPredicate::Special($prefix.to_string(), vec![
            $(
                $(( crate::nemo_model::ProtoBinding::NamedConnection(stringify!($var).to_string()) , $var_suffix.to_string() ))?
                $(( crate::nemo_model::ProtoBinding::Binding(crate::nemo_model::Binding::from(&$expr)) , $expr_suffix.to_string() ))?
            ),*
        ])
    };
}

macro_rules! nemo_condition {
    ($(?$first_var:ident)?$($first:expr)?, $sep:expr, $(?$second_var:ident)?$($second:expr)?) => {
        crate::nemo_model::ProtoPredicate::Special("".to_string(), vec![
            (
                $(( crate::nemo_model::ProtoBinding::NamedConnection(stringify!($first_var).to_string())))?
                $(( crate::nemo_model::ProtoBinding::Binding(crate::nemo_model::Binding::from(&$first))))?
                , ($sep).to_string()
            ),
            (
                $(( crate::nemo_model::ProtoBinding::NamedConnection(stringify!($second_var).to_string())))?
                $(( crate::nemo_model::ProtoBinding::Binding(crate::nemo_model::Binding::from(&$second))))?
                , "".to_string()
            )
        ])
    };
}

/// A NEMO rule
/// rules are always stored in [Predicate] instances
#[derive(Debug)]
pub struct Rule {
    /// bindings in predicate that has this rule as definition
    bindings: Vec<Binding>,
    /// rule body
    body: Vec<BoundPredicate>,
    /// filters
    filters: Vec<SpecialPredicate>,
}

impl Rule {
    pub fn new(bindings: Vec<Binding>, body: Vec<BoundPredicate>, filters: Vec<SpecialPredicate>) -> Rule{
        Rule{bindings, body, filters}
    }

    fn matches(&self, predicate: &Predicate) -> bool {
        self.bindings.len() == predicate.positions.len()
    }

    fn assert_matches(&self, predicate: &Predicate){
        assert!(
            self.matches(predicate),
            "Invalid number of arguments for Rule: Expected {} got {} .",
            predicate.positions.len(),
            self.bindings.len()
        );
    }

    fn construct_for(&self, predicate_name: &str, state: &mut GenState) -> String {
        let mut var_names = VariableTranslator::new();
        let head_inner = make_non_empty(self.bindings.iter()
            .map(|b| b.nemo_string(&mut var_names))
            .collect::<Vec<_>>()
            .join(", "));
        let body = self.body.iter()
            .map(|a| a.nemo_string(&mut var_names, state))
            .collect::<Vec<_>>()
            .join(", ");
        let filters = self.filters.iter()
            .map(|a| a.nemo_string(&mut var_names))
            .collect::<Vec<_>>()
            .join(", ");
        let mut result = format!("{predicate_name}({head_inner}) :- {body}");

        if !filters.is_empty() {
            result.push_str(", ");
            result.push_str(&filters);
        }
        result.push_str(" .");

        result
    }

    fn directly_influences(&self, pos: usize) -> HashSet<(PredicatePtr, usize)> {
        let binding = self.bindings.get(pos).expect(&format!("pos {pos} out of range; arity is {}", self.bindings.len()));
        match binding {
            Binding::Variable(_v) => {
                let mut result = HashSet::new();
                for bound_pred in &self.body {
                    if bound_pred.negated { continue };
                    for pos in bound_pred.bindings.iter().enumerate().filter(|(_i, b)| *b == binding).map(|(i, _b)| i) {
                        result.insert((bound_pred.predicate.clone(), pos));
                    }
                }
                result
            },
            _ => HashSet::new()
        }
    }
}

struct VariableTranslator {
    names: UniqueStrings,
    mapping: HashMap<VarPtr, String>
}

impl VariableTranslator {
    fn new() -> VariableTranslator {
        VariableTranslator{names: UniqueStrings::new(), mapping: HashMap::new()}
    }

    fn get(&mut self, variable: VarPtr) -> String {
        if let Some(s) = self.mapping.get(&variable) {
            return s.clone();
        }
        let label = variable.label();

        // handle invalid variable names
        let mut label_to_use = format!("var_{label}");
        if let Some(first_char) = label.chars().next() {
            if first_char.is_ascii_alphabetic() {
                label_to_use = label;
            }
        }

        let new_name = self.names.get(label_to_use);
        self.mapping.insert(variable, new_name.clone());
        new_name
    }
}

/// A NEMO fact
/// facts are stored in [Predicate] instances
#[derive(Debug)]
pub struct Fact {
    bindings: Vec<String>
}

impl Fact {
    pub fn new(bindings: Vec<String>) -> Fact {
        Fact{bindings}
    }

    fn matches(&self, predicate: &Predicate) -> bool {
        self.bindings.len() == predicate.positions.len()
    }

    fn assert_matches(&self, predicate: &Predicate){
        assert!(
            self.matches(predicate),
            "Invalid number of arguments for Fact: Expected {} got {}.",
            predicate.positions.len(),
            self.bindings.len()
        );
    }

    fn write_for(&self, predicate_name: &str, state: &mut GenState){
        state.add_line(format!(
            "{predicate_name}({}) .",
            make_non_empty(self.bindings.join(", "))
        ));
    }
}

/// A NEMO predicate
/// Two predicates with the same label are not the same
#[derive(Debug)]
struct Predicate {
    /// label is used in predicate name generation
    label: String,
    /// for general predicate positions
    positions: Vec<PredicatePos>,
    /// a predicate may depend on other predicates through rules
    rules: Vec<Rule>,
    /// a predicate may have some facts
    facts: Vec<Fact>
}

impl Predicate {
    pub fn new(label: &str, variables: Vec<VarPtr>) -> Self {
        Predicate{
            label: label.to_string(),
            positions: variables
                .iter()
                .map(|v| PredicatePos::new(v.clone()))
                .collect(),
            rules: vec![],
            facts: vec![],
        }
    }

    pub fn add_fact(&mut self, fact: Fact){
        fact.assert_matches(self);
        self.facts.push(fact);
    }

    pub fn add_rule(&mut self, rule: Rule){
        rule.assert_matches(self);
        self.rules.push(rule);
    }

    pub fn pos_at(&self, pos: usize) -> &PredicatePos {
        self.positions.get(pos).expect(&format!(
            "Invalid position {pos}, {} has arity {}",
            self.label,
            self.positions.len()
        ))
    }

    pub fn var_at(&self, pos: usize) -> VarPtr {
        self.pos_at(pos).variable.clone()
    }

    /// if property contains multiple one-bits they all must be satisfied ("and" check)
    pub fn property_at(&self, property: u32, pos: usize) -> bool {
        (self.pos_at(pos).properties & property) == property
    }

    pub fn unset_property(&mut self, property: u32, pos: usize) {
        let msg = format!(
            "Invalid position for unsetting property {property} at pos {pos}, {} has arity {}",
            self.label,
            self.positions.len()
        );
        let predicate_pos = self.positions.get_mut(pos).expect(&msg);
        predicate_pos.properties &= !property;
    }
}

struct UniqueStrings {
    generated: HashSet<String>
}

impl UniqueStrings {
    fn new() -> UniqueStrings{
        UniqueStrings{generated: HashSet::new()}
    }

    fn get(&mut self, base: String) -> String{
        let result = if self.generated.contains(&base) {
            let mut suffix = 1;
            while self.generated.contains(&format!("{base}_{suffix}")) { suffix += 1 };
            format!("{base}_{suffix}")
        }
        else { base };
        self.generated.insert(result.clone());
        result
    }
}

pub struct GenState{
    predicate_names: UniqueStrings,
    /// must include also predicates during generation
    already_generated_predicates: HashMap<PredicatePtr, String>,
    program_text: String,
}

impl GenState {
    pub fn new() -> GenState {
        GenState {
            program_text: String::new(),
            predicate_names: UniqueStrings::new(),
            already_generated_predicates: HashMap::new(),
        }
    }

    /// Register a new predicate as generated and return a unique name for it
    pub fn register(&mut self, predicate: PredicatePtr) -> String {
        assert!(
            !self.already_generated_predicates.contains_key(&predicate),
            "Predicate {} already registered. Are you generating its definition twice?",
            predicate.label()
        );
        let label = predicate.label();
        let name = self.predicate_names.get(label);
        self.already_generated_predicates.insert(predicate, name.clone());
        name
    }

    /// get unique name for given predicate, returns `None` if not [registered](GenState::register).
    /// Can also be used to determine if the predicate is registered.
    pub fn name(&self, predicate: &PredicatePtr) -> Option<String>{
        self.already_generated_predicates.get(predicate).cloned()
    }

    /// add new line to the program text
    pub fn add_line(&mut self, line: String){
        self.add(&line);
        self.lb();
    }

    /// add content to program text
    pub fn add(&mut self, text: &str){
        self.program_text.push_str(text);
    }

    /// add new line to program text
    pub fn lb(&mut self){
        self.program_text.push('\n');
    }

    pub fn to_string(self) -> String {
        self.program_text
    }
}

#[derive(Debug)]
pub struct PredicatePtr {
    ptr: Rc<RefCell<Predicate>>
}

impl PredicatePtr {
    pub fn clone(&self) -> PredicatePtr {
        PredicatePtr{ptr: self.ptr.clone()}
    }

    pub fn new(label: &str, variables: Vec<VarPtr>) -> PredicatePtr {
        PredicatePtr{ptr: Rc::new(RefCell::new(Predicate::new(label, variables)))}
    }

    pub fn add_fact(&self, fact: Fact){
        let mut p = self.ptr.borrow_mut();
        p.add_fact(fact);
    }

    pub fn add_rule(&self, rule: Rule){
        let mut p = self.ptr.borrow_mut();
        p.add_rule(rule);
    }

    pub fn label(&self) -> String {
        let p = self.ptr.borrow();
        p.label.clone()
    }

    pub fn vars(&self) -> Vec<VarPtr> {
        let p = self.ptr.borrow();
        p.positions.iter().map(|p| p.variable.clone()).collect()
    }

    pub fn var_at(&self, pos: usize) -> VarPtr {
        let p = self.ptr.borrow();
        p.var_at(pos)
    }

    fn directly_influences_pos(&self, pos: usize) -> HashSet<(PredicatePtr, usize)> {
        let p = self.ptr.borrow();
        p.rules.iter().flat_map(|r| r.directly_influences(pos)).collect()
    }

    pub fn influences_pos(&self, pos: usize) -> HashSet<(PredicatePtr, usize)> {
        let mut done: HashSet<(PredicatePtr, usize)> = HashSet::new();
        let mut doing: Vec<(PredicatePtr, usize)> = Vec::new();
        doing.push((self.clone(), pos));

        while let Some((pred, p)) = doing.pop() {
            for influencer in pred.directly_influences_pos(p) {
                if !done.contains(&influencer) && !doing.contains(&influencer) {
                    doing.push(influencer);
                }
            }
            done.insert((pred, p));
        }

        done
    }

    /// This is based on [Predicate::property_at]
    /// Additional properties are recursively collected from all [influencing positions](PredicatePtr::influences_pos).
    /// Note that only non-negated [explicit bindings](BoundPredicate) of [variables](Binding::Variable) are used to collect properties.
    /// The semantic of a property is that all bindings to a position must have the property.
    ///
    /// Example:
    ///     Suppose `is_even` property is defined as flag `1 << 3`.
    ///     The semantic would be that all bindings to a position must be even.
    ///     `a.property_at(is_even, 0)` is `true` by default.
    ///     A rule `a(?x) :- b(?x) .` would make it false if `b.property_at(is_even, 0)` is known to be false no matter other rules.
    ///     Explicitly [unsetting](PredicatePtr::unset_property) would also make it `false`.
    pub fn property_at(&self, property: u32, pos: usize) -> bool {
        let p = self.ptr.borrow();
        if !p.property_at(property, pos) { return false }
        for (dependency, dependency_pos) in self.influences_pos(pos) {
            let p = dependency.ptr.borrow();
            if !p.property_at(property, dependency_pos) {
                return false;
            }
        }
        return true;
    }

    pub fn unset_property(&self, property: u32, pos: usize) {
        let mut p = self.ptr.borrow_mut();
        p.unset_property(property, pos);
    }

    /// Gets NEMO program for the predicate including dependencies
    /// Returns predicate name in program. Get program text via [GenState::to_string()].
    pub fn construct_program(&self, state: &mut GenState) -> String {
        if let Some(n) = state.name(self) { return n };

        let name = state.register(self.clone());
        let p = self.ptr.borrow();

        for fact in &p.facts {fact.write_for(&name, state)}

        // first all rules are generated, then they are written *together* in the program
        let rules: Vec<String> = p.rules.iter().map(|r| r.construct_for(&name, state)).collect();
        state.add_line(rules.join("\n"));

        name
    }
}

impl PartialEq for PredicatePtr {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.ptr, &other.ptr)
    }
}
impl Eq for PredicatePtr {}

impl Hash for PredicatePtr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let ptr: *const RefCell<Predicate> = Rc::as_ptr(&self.ptr);
        ptr.hash(state);
    }
}

pub trait TypedPredicate: Debug {
    /// an implementation may want to replace some of the variables with new custom variables
    fn create(label: &str, variables: Vec<VarPtr>) -> Self where Self: Sized;
    fn create_dummy() -> Self where Self: Sized;
    fn get_predicate(&self) -> PredicatePtr;
    fn clone(&self) -> Self where Self: Sized;
    fn add_optional_named_binding(&self, name: &str) -> Box<dyn Fn(&mut RuleBuilder, ProtoBinding) + '_>;
}

pub fn add_fact(p: &dyn TypedPredicate, fact: Fact){
    p.get_predicate().add_fact(fact)
}

pub fn add_rule(p: &dyn TypedPredicate, rule: Rule){
    p.get_predicate().add_rule(rule)
}

pub fn get_vars(p: &dyn TypedPredicate) -> Vec<VarPtr>{
    p.get_predicate().vars()
}

pub fn has_prop(pred: &dyn TypedPredicate, prop: u32, pos: usize) -> bool { pred.get_predicate().property_at(prop, pos) }

pub fn has_prop_for_var(pred: &dyn TypedPredicate, prop: u32, var: &VarPtr) -> bool {
    let var_poses: Vec<_> = get_vars(pred).iter().enumerate().filter(|(_i, v)| *v == var).map(|(i, _v)| i).collect();
    for p in var_poses {
        if !has_prop(pred, prop, p){
            return false;
        }
    }
    return true;
}

pub fn to_bound_predicate(p: &dyn TypedPredicate) -> BoundPredicate {
    BoundPredicate::new(p.get_predicate(), get_vars(p).iter().map(Binding::from).collect(), false)
}

pub fn to_negated_bound_predicate(p: &dyn TypedPredicate) -> BoundPredicate {
    BoundPredicate::new(p.get_predicate(), get_vars(p).iter().map(Binding::from).collect(), true)
}

pub fn construct_program(p: &dyn TypedPredicate) -> String {
    let mut state = GenState::new();
    let output_rule = p.get_predicate().construct_program(&mut state);
    state.add_line(format!("@output {output_rule} ."));
    state.to_string()
}

/// A typed predicate that has no special positions
#[derive(Debug)]
pub struct Basic {
    /// The actual predicate
    inner: PredicatePtr
}

impl TypedPredicate for Basic {
    fn create(label: &str, variables: Vec<VarPtr>) -> Basic {
        Basic{inner: PredicatePtr::new(label, variables)}
    }

    fn create_dummy() -> Self where Self: Sized {
        Basic{inner: PredicatePtr::new("", vec![])}
    }

    fn get_predicate(&self) -> PredicatePtr {
        self.inner.clone()
    }

    fn clone(&self) -> Self where Self: Sized {
        Basic {inner: self.inner.clone()}
    }

    fn add_optional_named_binding(&self, _name: &str) -> Box<dyn Fn (&mut RuleBuilder, ProtoBinding) + '_> {
        Box::new(|_builder, _binding| {})
    }
}

impl From<&Basic> for ProtoPredicate {
    fn from(value: &Basic) -> Self {
        ProtoPredicate::from(value as &dyn TypedPredicate)
    }
}


/// A typed predicate that has a multiplicity as first position
#[derive(Debug)]
pub struct WithMultiplicity {
    /// The actual predicate
    inner: PredicatePtr
}

impl TypedPredicate for WithMultiplicity {
    fn create(label: &str, variables: Vec<VarPtr>) -> WithMultiplicity {
        assert!(variables.len() > 0, "predicate needs at least arity one for the multiplicity");
        let mut new_variables = vec![VarPtr::new("COUNT")];
        let mut vars = variables.into_iter();
        vars.next();
        new_variables.extend(vars);
        WithMultiplicity {inner: PredicatePtr::new(label, new_variables)}
    }

    fn create_dummy() -> Self where Self: Sized {
        WithMultiplicity{inner: PredicatePtr::new("", vec![])}
    }

    fn get_predicate(&self) -> PredicatePtr {
        self.inner.clone()
    }

    fn clone(&self) -> Self where Self: Sized {
        WithMultiplicity{inner: self.inner.clone()}
    }

    fn add_optional_named_binding(&self, name: &str) -> Box<dyn Fn(&mut RuleBuilder, ProtoBinding) + '_> {
        match name {
            "count" => Box::new(|builder, binding| self.count(builder, binding)),
            _ => Box::new(|_builder, _binding| {})
        }
    }
}

impl From<&WithMultiplicity> for ProtoPredicate {
    fn from(value: &WithMultiplicity) -> Self {
        ProtoPredicate::from(value as &dyn TypedPredicate)
    }
}

impl WithMultiplicity {
    fn count(&self, builder: &mut RuleBuilder, binding: ProtoBinding){
        builder.add_named_binding(binding, 0, "count", false)
    }
}


macro_rules! nemo_predicate_type {
    ($type_name:ident = $($pos_front:ident)* ... $($pos_back:ident)*) => {
        #[derive(Debug)]
        pub struct $type_name {
            /// The actual predicate
            inner: crate::nemo_model::PredicatePtr
        }

        impl crate::nemo_model::TypedPredicate for $type_name {
            fn create(label: &str, variables: Vec<crate::nemo_model::VarPtr>) -> $type_name {
                assert!(
                    variables.len() >= $type_name::FRONT_POSITIONS.len() + $type_name::BACK_POSITIONS.len(),
                    "predicate needs at least arity {} for [{} ... {}]",
                    $type_name::FRONT_POSITIONS.len() + $type_name::BACK_POSITIONS.len(),
                    $type_name::FRONT_POSITIONS.join(" "),
                    $type_name::BACK_POSITIONS.join(" ")
                );
                let new_variables = (
                        $type_name::FRONT_POSITIONS.iter()
                        .map(|v| crate::nemo_model::VarPtr::new(&v.to_uppercase()))
                    ).chain(
                        variables[$type_name::FRONT_POSITIONS.len()..variables.len() - $type_name::BACK_POSITIONS.len()].iter()
                        .map(|v| v.clone())
                    ).chain(
                        $type_name::BACK_POSITIONS.iter()
                        .map(|v| crate::nemo_model::VarPtr::new(&v.to_uppercase()))
                    ).collect();
                $type_name {inner: crate::nemo_model::PredicatePtr::new(label, new_variables)}
            }

            fn create_dummy() -> Self where Self: Sized {
                $type_name{inner: crate::nemo_model::PredicatePtr::new("", vec![])}
            }

            fn get_predicate(&self) -> crate::nemo_model::PredicatePtr {
                self.inner.clone()
            }

            fn clone(&self) -> Self where Self: Sized {
                $type_name{inner: self.inner.clone()}
            }

            fn add_optional_named_binding(&self, name: &str) -> Box<dyn Fn(&mut crate::nemo_model::RuleBuilder, crate::nemo_model::ProtoBinding) + '_> {
                match name {
                    $(
                        stringify!($pos_front) => Box::new(|builder, binding| self.$pos_front(builder, binding)),
                    )*
                    $(
                        stringify!($pos_back) => Box::new(|builder, binding| self.$pos_back(builder, binding)),
                    )*
                    _ => Box::new(|_builder, _binding| {})
                }
            }
        }

        impl From<&$type_name> for crate::nemo_model::ProtoPredicate {
            fn from(value: &$type_name) -> Self {
                crate::nemo_model::ProtoPredicate::from(value as &dyn crate::nemo_model::TypedPredicate)
            }
        }

        impl $type_name {
            const FRONT_POSITIONS:
                [&'static str; 0 $(+ stringify!($pos_front).len() * 0 + 1)*]
                = [$(stringify!($pos_front)),*];
            const BACK_POSITIONS:
                [&'static str; 0 $(+ stringify!($pos_back).len() * 0 + 1)*]
                = [$(stringify!($pos_back)),*];

            $(
                fn $pos_front (&self, builder: &mut crate::nemo_model::RuleBuilder, binding: crate::nemo_model::ProtoBinding){
                    builder.add_named_binding(
                        binding,
                        $type_name::FRONT_POSITIONS.iter().position(|p| *p == stringify!($pos_front)).unwrap(),
                        stringify!($pos_front),
                        false
                    )
                }
            )*

            $(
                fn $pos_back (&self, builder: &mut crate::nemo_model::RuleBuilder, binding: crate::nemo_model::ProtoBinding){
                    builder.add_named_binding(
                        binding,
                        $type_name::BACK_POSITIONS.len() - 1 - $type_name::BACK_POSITIONS.iter().position(|p| *p == stringify!($pos_back)).unwrap(),
                        stringify!($pos_back),
                        true
                    )
                }
            )*
        }
    };
}


#[derive(Clone)]
#[derive(Debug)]
pub enum ProtoBinding {
    Binding(Binding),
    NamedConnection(String),
    VariableSet(String),
    RenameSet(String),
    Aggregate(String, Vec<ProtoBinding>),
    BindingList(Vec<Binding>),
}

impl ProtoBinding {
    fn to_binding(self, default_var: Option<VarPtr>, variables: &mut HashMap<String, VarPtr>) -> Binding {
        match self {
            ProtoBinding::Binding(b) => b,
            ProtoBinding::NamedConnection(name) => {
                match variables.get(&name) {
                    Some(v) => Binding::Variable(v.clone()),
                    None => {
                        let var = default_var.expect(&format!("Connection variable {name} is not bound"));
                        variables.insert(name.clone(), var.clone());
                        Binding::Variable(var)
                    }
                }
            },
            ProtoBinding::VariableSet(_s) => panic!("VariableSet \"{_s}\" not resolved."),
            ProtoBinding::RenameSet(_s) => panic!("RenameSet \"{_s}\" not resolved."),
            ProtoBinding::BindingList(_l) => panic!("BindingList not resolved."),
            ProtoBinding::Aggregate(name, sub_bindings) => {
                Binding::Call(Call::new(
                    &format!("#{name}"),
                    sub_bindings.into_iter().map(|b| b.to_binding(None, variables)).collect()
                ))
            }
        }
    }

    fn resolve(&self, set_variables: Option<&HashMap<String, Vec<VarPtr>>>, rename_set_variables: Option<&HashMap<String, Vec<VarPtr>>>) -> Vec<ProtoBinding> {
        match self {
            ProtoBinding::Binding(_) | ProtoBinding::NamedConnection(_)  => vec![self.clone()],
            ProtoBinding::Aggregate(name, sub_bindings) => {
                vec![ProtoBinding::Aggregate(
                    name.clone(),
                    sub_bindings.iter()
                        .map(|b| b.resolve(set_variables, rename_set_variables))
                        .flatten()
                        .collect()
                )]
            },
            ProtoBinding::RenameSet(s) => {
                match rename_set_variables {
                    None => panic!("Rename set not allowed in this position."),
                    Some(translation) => {
                        let vars = translation.get(s).expect(&format!("Rename-set {s} not bound"));
                        let mut resolved_bindings = Vec::new();
                        for v in hash_dedup(vars) {
                            resolved_bindings.push(ProtoBinding::Binding(Binding::Variable(v)))
                        }
                        resolved_bindings
                    }
                }
            },
            ProtoBinding::VariableSet(s) => {
                let vars = set_variables
                    .expect("Unexpected VariableSet.")  // This would probably be an error in binding_parts or a function that forgot to use it
                    .get(s)
                    .expect(&format!("Var set {s} not bound"));
                let mut resolved_bindings = Vec::new();
                for v in hash_dedup(vars) {
                     resolved_bindings.push(ProtoBinding::Binding(Binding::Variable(v)))
                }
                resolved_bindings
            },
            ProtoBinding::BindingList(l) => {
                let mut resolved_bindings = Vec::new();
                for b in l {
                    resolved_bindings.push(ProtoBinding::Binding(b.clone()))
                }
                resolved_bindings
            }
        }
    }
}

impl<T> From<T> for ProtoBinding where Binding: From<T> {
    fn from(value: T) -> Self {
        ProtoBinding::Binding(Binding::from(value))
    }
}

impl From<TermSet> for ProtoBinding {
    fn from(value: TermSet) -> Self {
        ProtoBinding::BindingList(value.bindings())
    }
}

impl From<&TermSet> for ProtoBinding {
    fn from(value: &TermSet) -> Self {
        ProtoBinding::BindingList(value.bindings())
    }
}

/// allows duplication of a variable compared to a [TermSet]
impl From<&Vec<VarPtr>> for ProtoBinding {
    fn from(value: &Vec<VarPtr>) -> Self {
        ProtoBinding::BindingList(value.iter().map(|v| Binding::from(v)).collect())
    }
}

/// allows duplication of a binding compared to a [TermSet]
impl From<&Vec<Binding>> for ProtoBinding {
    fn from(value: &Vec<Binding>) -> Self {
        ProtoBinding::BindingList(value.iter().map(|v| v.clone()).collect())
    }
}

#[derive(Debug)]
pub enum ProtoPredicate {
    Explicit(PredicatePtr, Vec<ProtoBinding>, bool),
    Special(String, Vec<(ProtoBinding, String)>),
    Multi(Vec<ProtoPredicate>),
}

impl ProtoPredicate {
    fn compile(
        self,
        variables: &mut HashMap<String, VarPtr>,
        predicates: &mut Vec<BoundPredicate>,
        filters: &mut Vec<SpecialPredicate>,
    ) {
        match self {
            ProtoPredicate::Explicit(predicate, bindings, negated) => {
                predicates.push(
                    BoundPredicate::new(
                        predicate.clone(),
                        bindings.into_iter()
                            .enumerate()
                            .map(|(i, b)| b.to_binding(
                                Some(predicate.var_at(i)), variables
                            ))
                            .collect(),
                        negated
                    )
                )
            }
            ProtoPredicate::Special(prefix, bindings) => {
                filters.push(
                    SpecialPredicate::new(
                        prefix,
                        bindings.into_iter().map(
                            |(proto, suffix)|
                                (proto.to_binding(None, variables), suffix)
                        ).collect()
                    )
                )
            },
            ProtoPredicate::Multi(sub) => {
                for s in sub {
                    s.compile(variables, predicates, filters);
                }
            }
        }
    }

    pub fn flat_clone(&self) -> Vec<ProtoPredicate> {
        match self {
            ProtoPredicate::Explicit(head, body, negated) => vec![
                ProtoPredicate::Explicit(head.clone(), body.clone(), *negated)
            ],
            ProtoPredicate::Special(prefix, suffixes) => vec![
                ProtoPredicate::Special(prefix.clone(), suffixes.clone())
            ],
            ProtoPredicate::Multi(sub) => {
                let mut result = Vec::new();
                for s in sub {
                    result.extend(s.flat_clone())
                }
                result
            }
        }
    }
}

impl From<SpecialPredicate> for ProtoPredicate {
    fn from(value: SpecialPredicate) -> Self {
        ProtoPredicate::Special(
            value.prefix,
            value.bindings.into_iter().map(
                |(binding, suffix)| (ProtoBinding::Binding(binding), suffix)
            ).collect()
        )
    }
}

impl From<&dyn TypedPredicate> for ProtoPredicate {
    fn from(value: &dyn TypedPredicate) -> Self {
        ProtoPredicate::Explicit(
            value.get_predicate(),
            value.get_predicate().vars().iter()
                .map(
                    |v|
                    ProtoBinding::Binding(Binding::Variable(v.clone()))
                )
                .collect(),
            false
        )
    }
}

impl<T: TypedPredicate> From<&Vec<T>> for ProtoPredicate {
    fn from(value: &Vec<T>) -> Self {
        ProtoPredicate::Multi(value.iter().map(|p| ProtoPredicate::from(p as &dyn TypedPredicate)).collect())
    }
}

impl From<&BoundPredicate> for ProtoPredicate {
    fn from(value: &BoundPredicate) -> Self {
        ProtoPredicate::Explicit(value.predicate.clone(), value.bindings.iter().map(ProtoBinding::from).collect(), value.negated)
    }
}

impl From<Vec<ProtoPredicate>> for ProtoPredicate {
    fn from(value: Vec<ProtoPredicate>) -> Self {
        ProtoPredicate::Multi(value)
    }
}

macro_rules! nemo_atoms {
    ($($atom:expr),*) => {crate::nemo_model::ProtoPredicate::Multi(vec![
        $(crate::nemo_model::ProtoPredicate::from($atom)),*
    ])};
}

fn binding_parts<'a, 'b>(proto_bindings: &'a Vec<ProtoBinding>, vars: &'b Vec<VarPtr>) -> (&'a [ProtoBinding], &'b [VarPtr], &'a [ProtoBinding]) {
    let mut start_len = 0;
    let mut total_start_len = 0;
    let mut end_len = 0;
    let mut total_end_len = 0;
    let mut in_start = true;

    for b in proto_bindings {
        if in_start {
            match b {
                ProtoBinding::Binding(_) | ProtoBinding::NamedConnection(_) | ProtoBinding::Aggregate(_, _) => {start_len += 1; total_start_len += 1},
                ProtoBinding::BindingList(l) => {start_len += 1; total_start_len += l.len()},
                ProtoBinding::VariableSet(_) | ProtoBinding::RenameSet(_) => in_start = false
            }
        } else {
            match b {
                ProtoBinding::Binding(_) | ProtoBinding::NamedConnection(_) | ProtoBinding::Aggregate(_, _) => {end_len += 1; total_end_len += 1},
                ProtoBinding::BindingList(l) => {end_len += 1; total_end_len += l.len()},
                ProtoBinding::VariableSet(_) | ProtoBinding::RenameSet(_) => {
                    if end_len > 0 {panic!("Positional binding only allowed at start and end")}
                }
            }
        }
    }
    let var_strings: Vec<String> = vars.iter().map(|v| v.to_string()).collect();
    assert!(total_start_len <= vars.len(), "can not bind {} (front) variables to positions [{}]", start_len, var_strings.join(", "));
    assert!(total_start_len <= (vars.len() - total_end_len), "{} front and {} back variables are too much for [{}]", start_len, end_len, var_strings.join(", "));

    (
        &proto_bindings[..start_len],
        &vars[total_start_len..(vars.len() - total_end_len)],
        &proto_bindings[(proto_bindings.len() - end_len)..]
    )
}

fn variable_sets(proto_bindings: &Vec<ProtoBinding>) -> Vec<String>{
    let mut result: Vec<String> = Vec::new();
    for b in proto_bindings {
        match b {
            ProtoBinding::VariableSet(s) => result.push(s.clone()),
            _ => {}
        }
    }
    result
}

pub fn hash_dedup(vec: &Vec<VarPtr>) -> Vec<VarPtr>{
    let mut result = Vec::new();
    let mut done: HashSet<VarPtr> = HashSet::new();

    for v in vec {
        if !done.contains(&v) {
            done.insert(v.clone());
            result.push(v.clone());
        }
    }

    result
}


pub struct RuleBuilder {
    predicate_name: String,
    head: Vec<ProtoBinding>,
    body: Vec<ProtoPredicate>,
    partial_atom: Vec<ProtoBinding>,
    target_predicate: Option<PredicatePtr>,
    in_head: bool,
    expected_len: Option<usize>
}

impl RuleBuilder {
    pub fn new() -> RuleBuilder {
        RuleBuilder{
            predicate_name: String::new(),
            head: Vec::new(),
            body: Vec::new(),
            partial_atom: Vec::new(),
            target_predicate: None,
            in_head: true,
            expected_len: None
        }
    }

    pub fn new_for(predicate: PredicatePtr) -> RuleBuilder{
        let mut result = RuleBuilder::new();
        result.target_predicate = Some(predicate);
        result
    }

    pub fn start_body_atom(&mut self){
        if let Some(len) = self.expected_len {
            assert!(self.in_head, "expected_len should be reset in finalize_atom()");
            assert_eq!(self.head.len(), len, "There are bindings missing in the end of head.")
        }
        self.in_head = false;
        self.expected_len = None;
    }

    pub fn set_property_name(&mut self, name: &str){
        self.predicate_name = name.to_string()
    }

    pub fn add_head_binding(&mut self, binding: ProtoBinding){
        self.head.push(binding)
    }

    pub fn add_body_binding(&mut self, binding: ProtoBinding){
        self.partial_atom.push(binding)
    }

    pub fn add_named_binding(&mut self, binding: ProtoBinding, pos: usize, name: &str, in_back: bool) {
        let bindings = if self.in_head { &self.head } else {&self.partial_atom};
        let mut message = format!("{name} should be at pos {pos}");

        if in_back {
            message.push_str(" (counting from back)");
            let len_estimate = bindings.len() + 1 + pos;
            if let Some(len) = self.expected_len {
                assert_eq!(len_estimate, len, "Invalid Position in back: {message}");
            }
            else {
                self.expected_len = Some(len_estimate);
            }
        }
        else {
            assert_eq!(bindings.len(), pos, "Invalid Position in front: {message}");
        }

        if self.in_head {
            self.add_head_binding(binding)
        }
        else {
            self.add_body_binding(binding)
        }
    }

    pub fn finalize_atom(&mut self, predicate: PredicatePtr, negated: bool){
        let mut new_vec: Vec<ProtoBinding> = Vec::new();
        if let Some(len) = self.expected_len {
            assert_eq!(self.partial_atom.len(), len, "There are bindings missing in the end.");
            self.expected_len = None;
        }
        std::mem::swap(&mut new_vec, &mut self.partial_atom);
        self.body.push(ProtoPredicate::Explicit(predicate, new_vec, negated));
    }

    pub fn add_atom(&mut self, atom: ProtoPredicate) {
        self.body.push(atom);
    }

    pub fn add_negated_predicate(&mut self, predicate: &dyn TypedPredicate) {
        let atom = ProtoPredicate::from(predicate);
        match atom {
            ProtoPredicate::Explicit(predicate, bindings, negated) => {
                self.body.push(ProtoPredicate::Explicit(predicate, bindings, !negated));
            }
            _ => {panic!("ProtoPredicate from predicate should always be Explicit")}
        }
    }

    fn check(&self){
        assert!(self.partial_atom.is_empty(), "partial atom read");
        if let Some(_p) = &self.target_predicate {
            // uncomment to disallow using predicate under different name
            //assert_eq!(p.label(), self.predicate_name, "name mismatch");
        }
        else {
            assert!(!self.predicate_name.is_empty(), "predicate name not set");
        }
    }

    fn resolve_variable_sets(&self) -> (Vec<ProtoBinding>, Vec<ProtoPredicate>){
        let mut var_predicates: HashMap<VarPtr, u64> = HashMap::new();
        let mut set_predicates: HashMap<String, u64> = HashMap::new();
        let mut predicates_with_rename_set: HashSet<usize> = HashSet::new();

        // flatten body (remove multi proto predicates)
        let flat_body: Vec<ProtoPredicate> = self.body.iter().flat_map(
            |p| p.flat_clone()
        ).collect();

        // compute which predicate contains which variables and var set bindings
        // handle head
        if let Some(target) = &self.target_predicate {
            let target_vars = target.vars();
            let (_start, middle_vars, _end) = binding_parts(&self.head, &target_vars);
            for var in middle_vars {
                var_predicates.insert(var.clone(), 1);
            }
            for binding in &self.head {
                 match binding {
                    ProtoBinding::VariableSet(s) => {
                        set_predicates.insert(s.clone(), 1);
                    }
                    _ => {}
                }
            }
        }

        // handle body
        for (i, proto_predicate) in flat_body.iter().enumerate() {
            let flag: u64 = { 2u64 }.checked_pow((i + 1) as u32).expect("long predicate lists are not supported");
            match proto_predicate {
                ProtoPredicate::Explicit(predicate, bindings, _negated) => {
                    // check for rename set
                    let mut has_rename_set = false;
                    for proto_binding in bindings{
                        match proto_binding {
                            ProtoBinding::RenameSet(_) => {has_rename_set = true},
                            _ => {}
                        }
                    }
                    if has_rename_set {
                        predicates_with_rename_set.insert(i);
                        continue;
                        // predicates with rename set don't provide information which variable goes into which set because the variable could be part of the rename set
                    }

                    // set vars vor this predicate
                    let predicate_vars = predicate.vars();
                    let (_start, middle_vars, _end) = binding_parts(bindings, &predicate_vars);
                    for var in middle_vars {
                        let current_predicates = *var_predicates.get(var).unwrap_or(&0);
                        var_predicates.insert(var.clone(), current_predicates | flag);
                    }

                    // set var sets for this predicate
                    for proto_binding in bindings{
                        match proto_binding {
                            ProtoBinding::VariableSet(s) => {
                                let current_predicates = *set_predicates.get(s).unwrap_or(&0);
                                set_predicates.insert(s.clone(), current_predicates | flag);
                            }
                            _ => {}
                        }
                    }
                },
                ProtoPredicate::Special(_prefix, _bindings) => {
                    // special predicates don't have predicate_vars therefore they can not have
                    // variable sets
                }
                ProtoPredicate::Multi(_) => panic!("flat body should not contain multi")
            }
        }
        let set_index: HashMap<_, _> = set_predicates.into_iter().map(|(k, v)| (v, k)).collect();

        // Resolve variable sets in body
        let mut new_body: Vec<ProtoPredicate> = Vec::new();
        let mut set_variables: HashMap<String, Vec<VarPtr>> = HashMap::new();
        for (i, proto_predicate) in flat_body.iter().enumerate() {
            if predicates_with_rename_set.contains(&i) {
                // predicates with rename sets don't determine which variable belongs to which set (act like the head for `nemo_def!`) and are handled later
                continue;
            }
            match proto_predicate {
                ProtoPredicate::Explicit(predicate, bindings, negated) => {
                    let predicate_vars = predicate.vars();
                    let (start, middle_vars, end) = binding_parts(bindings, &predicate_vars);
                    let mut new_bindings: Vec<ProtoBinding> = Vec::new();
                    new_bindings.extend(start.iter().flat_map(|b| b.resolve(None, None)));
                    for var in middle_vars {
                        let predicates = *var_predicates.get(var).expect("predicates for var not computed.");
                        if let Some(var_set) = set_index.get(&predicates) {
                            new_bindings.push(ProtoBinding::Binding(Binding::Variable(var.clone())));
                            set_variables.entry(var_set.clone()).or_insert_with(Vec::new).push(var.clone());
                        } else {
                            // construct error message and panic
                            let flags = *var_predicates.get(var).unwrap();
                            let mut predicates: Vec<String> = Vec::new();
                            if flags & 1 > 0 {predicates.push("RULE_HEAD".to_string())}
                            for (i, proto_predicate) in self.body.iter().enumerate() {
                                let flag: u64 = { 2u64 }.pow((i + 1) as u32);
                                if flag & flags > 0 {
                                    match proto_predicate {
                                        ProtoPredicate::Explicit(p, bindings, _) => predicates.push(
                                            format!(
                                                "{}({})",
                                                p.label(),
                                                bindings.iter().map(
                                                    |b| match b {
                                                        ProtoBinding::VariableSet(s) => s.clone(),
                                                        ProtoBinding::Binding(_b) => "binding".to_string(),
                                                        ProtoBinding::RenameSet(_r) => "rename_set".to_string(),
                                                        ProtoBinding::Aggregate(_a, _b) => "aggregation".to_string(),
                                                        ProtoBinding::NamedConnection(s) => s.clone(),
                                                        ProtoBinding::BindingList(_l) => "binding_list".to_string(),
                                                    }
                                                ).collect::<Vec<_>>().join(", ")
                                            )
                                        ),
                                        _ => predicates.push("IMPLICIT".to_string()),
                                    };
                                }
                            }

                            let mut available = String::new();
                            for (key, value) in set_index.iter() {
                                available.push_str(&format!("{}: {:#b}\n", value, key));
                            }
                            panic!("var {var} in {} could not be bound to any var set; predicates: {} \nflags: {:#b} \navailable: \n{}\n", predicate.label(), predicates.join(", "), flags, available)
                        }
                    }
                    // ensure also empty variable sets exist (var sets that don't exist raise error when resolving head)
                    for var_set in variable_sets(bindings) {
                        set_variables.entry(var_set).or_insert_with(Vec::new);
                    }
                    new_bindings.extend(end.iter().flat_map(|b| b.resolve(None, None)));
                    new_body.push(ProtoPredicate::Explicit(predicate.clone(), new_bindings, *negated))
                },
                ProtoPredicate::Special(prefix, bindings) => {
                    for (binding, _suffix) in bindings {
                        match binding {
                            ProtoBinding::Aggregate(_, _) | ProtoBinding::Binding(_) | ProtoBinding::NamedConnection(_) => {}, // allowed
                            ProtoBinding::VariableSet(_) | ProtoBinding::RenameSet(_) | ProtoBinding::BindingList(_) => {panic!("rename sets, term sets and variable sets not allowed in special predicates")}
                        }
                    }
                    new_body.push(ProtoPredicate::Special(prefix.clone(), bindings.clone()));
                },
                ProtoPredicate::Multi(_) => panic!("flat body should not contain multi")
            }
        }

        // resolve and rename sets in body
        let mut rename_set_variables: HashMap<String, Vec<VarPtr>> = HashMap::new();
        for (i, proto_predicate) in flat_body.iter().enumerate() {
            if !predicates_with_rename_set.contains(&i) {
                // predicates without rename sets are already handled
                continue;
            }
            match proto_predicate {
                ProtoPredicate::Explicit(predicate, bindings, negated) => {
                    let mut my_var_sets: Vec<String> = Vec::new();
                    let mut my_rename_set: Option<String> = None;
                    for binding in bindings {
                        match binding {
                            ProtoBinding::VariableSet(s) => my_var_sets.push(s.clone()),
                            ProtoBinding::RenameSet(s) => {my_rename_set = Some(s.clone())}
                            _ => {}
                        }
                    }
                    let my_rename_set = my_rename_set.expect("predicate with rename set must by definition have a rename set");

                    let predicate_vars = predicate.vars();
                    let (start, middle_vars, end) = binding_parts(bindings, &predicate_vars);
                    let mut new_bindings: Vec<ProtoBinding> = Vec::new();
                    new_bindings.extend(start.iter().cloned());
                    for var in middle_vars {
                        let predicates = var_predicates.get(var);
                        let var_set = predicates
                            .map(|p| set_index.get(&p).expect("if variable occurs also in some predicate without rename set, it should be in some var set"));
                        let matched = var_set.filter(|var_set| my_var_sets.contains(var_set)).is_some();
                        if matched {
                            new_bindings.push(ProtoBinding::Binding(Binding::Variable(var.clone())))
                        }
                        else {
                            new_bindings.push(ProtoBinding::Binding(Binding::Variable(var.distinct_new())));
                            rename_set_variables.entry(my_rename_set.clone()).or_insert_with(Vec::new).push(var.clone());
                        }
                    }
                    new_bindings.extend(end.iter().cloned());
                    new_body.push(ProtoPredicate::Explicit(predicate.clone(), new_bindings, *negated))
                },
                ProtoPredicate::Special(_, _) => panic!("rename sets can only occur in explicit proto predicates and not in filters"),
                ProtoPredicate::Multi(_) => panic!("flat body should not contain multi"),
            }
        }

        // resolve head
        let mut new_head: Vec<ProtoBinding> = Vec::new();
        if let Some(target) = &self.target_predicate {
            let predicate_vars = target.vars();
            let (start, middle_vars, end) = binding_parts(&self.head, &predicate_vars);
            new_head.extend(
                start.iter().cloned().map(|proto_binding| proto_binding.resolve(Some(&set_variables), None)).flatten()
            );
            for var in middle_vars {
                let predicates = *var_predicates.get(var).expect("predicates for var in head not computed.");
                if set_index.get(&predicates).is_some() {
                    new_head.push(ProtoBinding::Binding(Binding::Variable(var.clone())))
                }
                else {
                    panic!("{var} not found in body")
                }
            }
            new_head.extend(
                end.iter().cloned().map(|proto_binding| proto_binding.resolve(Some(&set_variables), None)).flatten()
            );
        } else {
            new_head.extend(
                self.head.iter().map(|binding| binding.resolve(Some(&set_variables), Some(&rename_set_variables))).flatten()
            );
        }

        (new_head, new_body)
    }

    fn to_rule(self) -> Rule {
        let (proto_head, proto_body) = self.resolve_variable_sets();
        let mut name_lookup: HashMap<String, VarPtr> = HashMap::new();
        let mut predicates: Vec<BoundPredicate> = Vec::new();
        let mut filters: Vec<SpecialPredicate> = Vec::new();

        for proto_predicate in proto_body {
            proto_predicate.compile(&mut name_lookup, &mut predicates, &mut filters)
        }

        let mut head: Vec<Binding> = Vec::new();
        for proto_binding in proto_head {
            head.push(proto_binding.to_binding(None, &mut name_lookup))
        }

        if predicates.is_empty() {
            let dummy = Basic::create("dummy", vec![]);
            add_fact(&dummy, Fact::new(vec![]));
            predicates.push(BoundPredicate::new(dummy.get_predicate(), vec![], false));
        }

        Rule::new(head, predicates, filters)
    }

    pub fn to_predicate<T: TypedPredicate>(self) -> T {
        self.check();
        let name = self.predicate_name.clone();
        let rule = self.to_rule();

        let result = T::create(
            &name,
            rule.bindings.iter().map(|b| b.variable()).collect()
        );
        result.get_predicate().add_rule(rule);
        result
    }

    pub fn perform_add(self){
        self.check();
        let target = match &self.target_predicate {
            None => panic!("no target specified"),
            Some(t) => t.clone()
        };
        let rule = self.to_rule();
        target.add_rule(rule);
    }
}

macro_rules! nemo_declare {
    ($name:ident($($arg:ident),*)) => {
        let $name = crate::nemo_model::Basic::create(stringify!($name), vec![$($arg),*]);
    };
    ($name:ident($($arg:ident),*); $type:ty) => {
        let $name = <$type>::create(stringify!($name), vec![$($arg),*]);
    };
}

macro_rules! nemo_def {
    ($name:ident($($arg:expr),*)) => {
        let bindings: Vec<String> = vec![$(crate::nemo_model::Binding::from(&$arg)),*].iter().map(|binding|
            match binding {
                crate::nemo_model::Binding::Constant(c) => c.clone(),
                _ => panic!("Fact bindings should be constants (got {:?})", binding),
            }
        ).collect();
        let $name = crate::nemo_model::Basic::create(stringify!($name), bindings.iter().map(|_b| VarPtr::new("v")).collect());
        crate::nemo_model::add_fact(&$name,
            crate::nemo_model::Fact::new(bindings)
        )
    };
    ( // pattern duplicated for nemo_add but without type
        $head_name:ident(
            $(
                $(
                    $(@$head_key_front:ident)?$(@?$head_key_front_optional:ident)?:
                        $(?$head_connection_name_front:ident)?
                        $(%$head_aggregate_front:ident(
                            $(
                                $(??$head_aggregate_front_var_set:ident)?
                                $(?$head_aggregate_front_connection_name:ident)?
                                $($head_aggregate_front_expression:expr)?
                            ),+
                        ))?
                        $($head_expression_front:expr)?
                ),+;
            )?

            $(
                $(??$head_var_set:ident)?
                $(?$head_connection_name:ident)?
                $(%$head_aggregate:ident(
                    $(
                        $(??$head_aggregate_var_set:ident)?
                        $(?$head_aggregate_connection_name:ident)?
                        $($head_aggregate_expression:expr)?
                    ),+
                ))?
                $($head_expression:expr)?
            ),*

            $(
                ;$(
                    $(@$head_key_back:ident)?$(@?$head_key_back_optional:ident)?:
                        $(?$head_connection_name_back:ident)?
                        $(%$head_aggregate_back:ident(
                            $(
                                $(??$head_aggregate_back_var_set:ident)?
                                $(?$head_aggregate_back_connection_name:ident)?
                                $($head_aggregate_back_expression:expr)?
                            ),+
                        ))?
                        $($head_expression_back:expr)?
                ),+
            )?

        ) :- $(
            $(
                $body_predicate:ident(
                    $(
                        $(
                            $(@$body_key_front:ident)?$(@?$body_key_front_optional:ident)?:
                                $(?$body_connection_name_front:ident)?
                                $($body_expression_front:expr)?
                        ),+;
                    )?
                    $(
                        $(??*$rename_set:ident)?
                        $(??$body_var_set:ident)?
                        $(?$body_connection_name:ident)?
                        $($body_expression:expr)?
                    ),*
                    $(
                         ;$(
                            $(@$body_key_back:ident)?$(@?$body_key_back_optional:ident)?:
                                $(?$body_connection_name_back:ident)?
                                $($body_expression_back:expr)?
                        ),+
                    )?
                )
            )?
            $(
                ~$negated_body_predicate:ident(
                    $(
                        $(
                            $(@$negated_body_key_front:ident)?$(@?$negated_body_key_front_optional:ident)?:
                                $(?$negated_body_connection_name_front:ident)?
                                $($negated_body_expression_front:expr)?
                        ),+;
                    )?
                    $(
                        $(??*$negated_rename_set:ident)?
                        $(??$negated_body_var_set:ident)?
                        $(?$negated_body_connection_name:ident)?
                        $($negated_body_expression:expr)?
                    ),*
                    $(
                         ;$(
                            $(@$negated_body_key_back:ident)?$(@?$negated_body_key_back_optional:ident)?:
                                $(?$negated_body_connection_name_back:ident)?
                                $($negated_body_expression_back:expr)?
                        ),+
                    )?
                )
            )?
            $($atom_expression:block)?
            $(~$negated_atom_expression:block)?
        ),+; $predicate_type:ty $(; $predicate_name:expr)?
    ) => {
        let mut builder = crate::nemo_model::RuleBuilder::new();
        #[allow(unused_variables)]
        let head_predicate = <$predicate_type>::create_dummy();

        builder.set_property_name(stringify!($head_name));
        $(builder.set_property_name($predicate_name);)?
        /*
        This block is duplicated also at nemo_add.

        The reason for this is that IDE support when calling nested macros is limited.
        ----- DUPLICATED BLOCK -----
         */
        // HEAD
        // head-front
        $(
            $(
                head_predicate.$( $head_key_front )?$( add_optional_named_binding(stringify!($head_key_front_optional)) )?(
                    &mut builder,
                    $(
                        crate::nemo_model::ProtoBinding::NamedConnection(
                            stringify!($head_connection_name_front).to_string()
                        )
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::from(&$head_expression_front)
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::Aggregate(
                            stringify!($head_aggregate_front).to_string(),
                            vec![$(
                                $(
                                    crate::nemo_model::ProtoBinding::NamedConnection(
                                        stringify!($head_aggregate_front_connection_name).to_string()
                                    )
                                )?
                                $(
                                    crate::nemo_model::ProtoBinding::VariableSet(
                                        stringify!($head_aggregate_front_var_set).to_string()
                                    )
                                )?
                                $(
                                    crate::nemo_model::ProtoBinding::from(&$head_aggregate_front_expression)
                                )?
                            ),+]
                        )
                    )?
                );
            )+
        )?

        // head-middle
        $(
            builder.add_head_binding(
                $(
                    crate::nemo_model::ProtoBinding::NamedConnection(
                        stringify!($head_connection_name).to_string()
                    )
                )?
                $(
                    crate::nemo_model::ProtoBinding::VariableSet(
                        stringify!($head_var_set).to_string()
                    )
                )?
                $(
                    crate::nemo_model::ProtoBinding::from(&$head_expression)
                )?
                $(
                    crate::nemo_model::ProtoBinding::Aggregate(
                        stringify!($head_aggregate).to_string(),
                        vec![$(
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($head_aggregate_connection_name).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::VariableSet(
                                    stringify!($head_aggregate_var_set).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$head_aggregate_expression)
                            )?
                        ),+]
                    )
                )?
            );
        )*

        // head-back
        $(
            $(
                head_predicate.$($head_key_back)?$( add_optional_named_binding(stringify!($head_key_back_optional)) )?(
                    &mut builder,
                    $(
                        crate::nemo_model::ProtoBinding::NamedConnection(
                            stringify!($head_connection_name_back).to_string()
                        )
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::from(&$head_expression_back)
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::Aggregate(
                            stringify!($head_aggregate_back).to_string(),
                            vec![$(
                                $(
                                    crate::nemo_model::ProtoBinding::NamedConnection(
                                        stringify!($head_aggregate_back_connection_name).to_string()
                                    )
                                )?
                                $(
                                    crate::nemo_model::ProtoBinding::VariableSet(
                                        stringify!($head_aggregate_back_var_set).to_string()
                                    )
                                )?
                                $(
                                    crate::nemo_model::ProtoBinding::from(&$head_aggregate_back_expression)
                                )?
                            ),+]
                        )
                    )?
                );
            )+
        )?

        // BODY
        $(
            // body attoms
            $(
                builder.start_body_atom();
                // attom front
                $(
                    $(
                        {&$body_predicate}.$($body_key_front)?$( add_optional_named_binding(stringify!($body_key_front_optional)) )?(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($body_connection_name_front).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$body_expression_front)
                            )?
                        );
                    )+
                )?

                // attom middle
                $(
                    builder.add_body_binding(
                        $(
                            crate::nemo_model::ProtoBinding::NamedConnection(
                                stringify!($body_connection_name).to_string()
                            )
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::VariableSet(
                                stringify!($body_var_set).to_string()
                            )
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::from(&$body_expression)
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::RenameSet(
                                stringify!($rename_set).to_string()
                            )
                        )?
                    );
                )*

                // attom back
                $(
                    $(
                        {&$body_predicate}.$($body_key_back)?$( add_optional_named_binding(stringify!($body_key_back_optional)) )?(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($body_connection_name_back).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$body_expression_back)
                            )?
                        );
                    )+
                )?

                builder.finalize_atom({&$body_predicate}.get_predicate(), false);
            )?

            // negated body attoms
            $(
                builder.start_body_atom();
                // attom front
                $(
                    $(
                        {&$negated_body_predicate}.$($negated_body_key_front)?$( add_optional_named_binding(stringify!($negated_body_key_front_optional)) )?(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($negated_body_connection_name_front).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$negated_body_expression_front)
                            )?
                        );
                    )+
                )?

                // attom middle
                $(
                    builder.add_body_binding(
                        $(
                            crate::nemo_model::ProtoBinding::NamedConnection(
                                stringify!($negated_body_connection_name).to_string()
                            )
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::VariableSet(
                                stringify!($negated_body_var_set).to_string()
                            )
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::from(&$negated_body_expression)
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::RenameSet(
                                stringify!($negated_rename_set).to_string()
                            )
                        )?
                    );
                )*

                // attom back
                $(
                    $(
                        {&$negated_body_predicate}.$($negated_body_key_back)?$( add_optional_named_binding(stringify!($negated_body_key_back_optional)) )?(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($negated_body_connection_name_back).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$negated_body_expression_back)
                            )?
                        );
                    )+
                )?

                builder.finalize_atom({&$negated_body_predicate}.get_predicate(), true);
            )?

            // body filters / predicate expressions
            $(
                builder.add_atom(crate::nemo_model::ProtoPredicate::from($atom_expression));
            )?
            $(
                builder.add_negated_predicate($negated_atom_expression);
            )?
        )+
        /*
        ----- END OF DUPLICATED BLOCK -----
         */

        let $head_name = builder.to_predicate::<$predicate_type>();
    };
}

macro_rules! nemo_add {
    ($name:ident($($arg:expr),*)) => {
        let bindings = vec![$(crate::nemo_model::Binding::from(&$arg)),*].iter().map(|binding|
            match binding {
                crate::nemo_model::Binding::Constant(c) => c.clone(),
                _ => panic!("Fact bindings should be constants (got {:?})", binding),
            }
        ).collect();
        crate::nemo_model::add_fact(&$name,
            crate::nemo_model::Fact::new(bindings)
        )
    };
    ( // pattern duplicated for nemo_def but with type
        $head_name:ident(
            $(
                $(
                    $(@$head_key_front:ident)?$(@?$head_key_front_optional:ident)?:
                        $(?$head_connection_name_front:ident)?
                        $(%$head_aggregate_front:ident(
                            $(
                                $(??$head_aggregate_front_var_set:ident)?
                                $(?$head_aggregate_front_connection_name:ident)?
                                $($head_aggregate_front_expression:expr)?
                            ),+
                        ))?
                        $($head_expression_front:expr)?
                ),+;
            )?

            $(
                $(??$head_var_set:ident)?
                $(?$head_connection_name:ident)?
                $(%$head_aggregate:ident(
                    $(
                        $(??$head_aggregate_var_set:ident)?
                        $(?$head_aggregate_connection_name:ident)?
                        $($head_aggregate_expression:expr)?
                    ),+
                ))?
                $($head_expression:expr)?
            ),*

            $(
                ;$(
                    $(@$head_key_back:ident)?$(@?$head_key_back_optional:ident)?:
                        $(?$head_connection_name_back:ident)?
                        $(%$head_aggregate_back:ident(
                            $(
                                $(??$head_aggregate_back_var_set:ident)?
                                $(?$head_aggregate_back_connection_name:ident)?
                                $($head_aggregate_back_expression:expr)?
                            ),+
                        ))?
                        $($head_expression_back:expr)?
                ),+
            )?

        ) :- $(
            $(
                $body_predicate:ident(
                    $(
                        $(
                            $(@$body_key_front:ident)?$(@?$body_key_front_optional:ident)?:
                                $(?$body_connection_name_front:ident)?
                                $($body_expression_front:expr)?
                        ),+;
                    )?
                    $(
                        $(??*$rename_set:ident)?
                        $(??$body_var_set:ident)?
                        $(?$body_connection_name:ident)?
                        $($body_expression:expr)?
                    ),*
                    $(
                         ;$(
                            $(@$body_key_back:ident)?$(@?$body_key_back_optional:ident)?:
                                $(?$body_connection_name_back:ident)?
                                $($body_expression_back:expr)?
                        ),+
                    )?
                )
            )?
            $(
                ~$negated_body_predicate:ident(
                    $(
                        $(
                            $(@$negated_body_key_front:ident)?$(@?$negated_body_key_front_optional:ident)?:
                                $(?$negated_body_connection_name_front:ident)?
                                $($negated_body_expression_front:expr)?
                        ),+;
                    )?
                    $(
                        $(??*$negated_rename_set:ident)?
                        $(??$negated_body_var_set:ident)?
                        $(?$negated_body_connection_name:ident)?
                        $($negated_body_expression:expr)?
                    ),*
                    $(
                         ;$(
                            $(@$negated_body_key_back:ident)?$(@?$negated_body_key_back_optional:ident)?:
                                $(?$negated_body_connection_name_back:ident)?
                                $($negated_body_expression_back:expr)?
                        ),+
                    )?
                )
            )?
            $($atom_expression:block)?
            $(~$negated_atom_expression:block)?
        ),+
    ) => {
        let mut builder = crate::nemo_model::RuleBuilder::new_for({&$head_name}.get_predicate());
        #[allow(unused_variables)]
        let head_predicate = {&$head_name};
        builder.set_property_name(stringify!($head_name));
        /*
        This block is duplicated also at nemo_def.

        The reason for this is that IDE support when calling nested macros is limited.
        ----- DUPLICATED BLOCK -----
         */
        // HEAD
        // head-front
        $(
            $(
                head_predicate.$( $head_key_front )?$( add_optional_named_binding(stringify!($head_key_front_optional)) )?(
                    &mut builder,
                    $(
                        crate::nemo_model::ProtoBinding::NamedConnection(
                            stringify!($head_connection_name_front).to_string()
                        )
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::from(&$head_expression_front)
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::Aggregate(
                            stringify!($head_aggregate_front).to_string(),
                            vec![$(
                                $(
                                    crate::nemo_model::ProtoBinding::NamedConnection(
                                        stringify!($head_aggregate_front_connection_name).to_string()
                                    )
                                )?
                                $(
                                    crate::nemo_model::ProtoBinding::VariableSet(
                                        stringify!($head_aggregate_front_var_set).to_string()
                                    )
                                )?
                                $(
                                    crate::nemo_model::ProtoBinding::from(&$head_aggregate_front_expression)
                                )?
                            ),+]
                        )
                    )?
                );
            )+
        )?

        // head-middle
        $(
            builder.add_head_binding(
                $(
                    crate::nemo_model::ProtoBinding::NamedConnection(
                        stringify!($head_connection_name).to_string()
                    )
                )?
                $(
                    crate::nemo_model::ProtoBinding::VariableSet(
                        stringify!($head_var_set).to_string()
                    )
                )?
                $(
                    crate::nemo_model::ProtoBinding::from(&$head_expression)
                )?
                $(
                    crate::nemo_model::ProtoBinding::Aggregate(
                        stringify!($head_aggregate).to_string(),
                        vec![$(
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($head_aggregate_connection_name).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::VariableSet(
                                    stringify!($head_aggregate_var_set).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$head_aggregate_expression)
                            )?
                        ),+]
                    )
                )?
            );
        )*

        // head-back
        $(
            $(
                head_predicate.$($head_key_back)?$( add_optional_named_binding(stringify!($head_key_back_optional)) )?(
                    &mut builder,
                    $(
                        crate::nemo_model::ProtoBinding::NamedConnection(
                            stringify!($head_connection_name_back).to_string()
                        )
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::from(&$head_expression_back)
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::Aggregate(
                            stringify!($head_aggregate_back).to_string(),
                            vec![$(
                                $(
                                    crate::nemo_model::ProtoBinding::NamedConnection(
                                        stringify!($head_aggregate_back_connection_name).to_string()
                                    )
                                )?
                                $(
                                    crate::nemo_model::ProtoBinding::VariableSet(
                                        stringify!($head_aggregate_back_var_set).to_string()
                                    )
                                )?
                                $(
                                    crate::nemo_model::ProtoBinding::from(&$head_aggregate_back_expression)
                                )?
                            ),+]
                        )
                    )?
                );
            )+
        )?

        // BODY
        $(
            // body attoms
            $(
                builder.start_body_atom();
                // attom front
                $(
                    $(
                        {&$body_predicate}.$($body_key_front)?$( add_optional_named_binding(stringify!($body_key_front_optional)) )?(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($body_connection_name_front).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$body_expression_front)
                            )?
                        );
                    )+
                )?

                // attom middle
                $(
                    builder.add_body_binding(
                        $(
                            crate::nemo_model::ProtoBinding::NamedConnection(
                                stringify!($body_connection_name).to_string()
                            )
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::VariableSet(
                                stringify!($body_var_set).to_string()
                            )
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::from(&$body_expression)
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::RenameSet(
                                stringify!($rename_set).to_string()
                            )
                        )?
                    );
                )*

                // attom back
                $(
                    $(
                        {&$body_predicate}.$($body_key_back)?$( add_optional_named_binding(stringify!($body_key_back_optional)) )?(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($body_connection_name_back).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$body_expression_back)
                            )?
                        );
                    )+
                )?

                builder.finalize_atom({&$body_predicate}.get_predicate(), false);
            )?

            // negated body attoms
            $(
                builder.start_body_atom();
                // attom front
                $(
                    $(
                        {&$negated_body_predicate}.$($negated_body_key_front)?$( add_optional_named_binding(stringify!($negated_body_key_front_optional)) )?(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($negated_body_connection_name_front).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$negated_body_expression_front)
                            )?
                        );
                    )+
                )?

                // attom middle
                $(
                    builder.add_body_binding(
                        $(
                            crate::nemo_model::ProtoBinding::NamedConnection(
                                stringify!($negated_body_connection_name).to_string()
                            )
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::VariableSet(
                                stringify!($negated_body_var_set).to_string()
                            )
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::from(&$negated_body_expression)
                        )?
                        $(
                            crate::nemo_model::ProtoBinding::RenameSet(
                                stringify!($negated_rename_set).to_string()
                            )
                        )?
                    );
                )*

                // attom back
                $(
                    $(
                        {&$negated_body_predicate}.$($negated_body_key_back)?$( add_optional_named_binding(stringify!($negated_body_key_back_optional)) )?(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($negated_body_connection_name_back).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::from(&$negated_body_expression_back)
                            )?
                        );
                    )+
                )?

                builder.finalize_atom({&$negated_body_predicate}.get_predicate(), true);
            )?

            // body filters / predicate expressions
            $(
                builder.add_atom(crate::nemo_model::ProtoPredicate::from($atom_expression));
            )?
            $(
                builder.add_negated_predicate($negated_atom_expression);
            )?
        )+
        /*
        ----- END OF DUPLICATED BLOCK -----
         */

        builder.perform_add();
    };
}

pub(crate) use nemo_declare;
pub(crate) use nemo_add;
pub(crate) use nemo_def;
pub(crate) use nemo_predicate_type;
pub(crate) use nemo_var;
pub(crate) use nemo_iri;
pub(crate) use nemo_call;
pub(crate) use nemo_filter;
pub(crate) use nemo_condition;
pub(crate) use nemo_terms;
pub(crate) use nemo_atoms;
