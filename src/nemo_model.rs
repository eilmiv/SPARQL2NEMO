use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter, Write};
use std::hash::{Hash, Hasher};
use std::ops;
use std::rc::Rc;

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
    ($label:ident) => {crate::nemo_model::Variable::create(stringify!($label))};
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
    /// flags to track properties of that position
    properties: u32,
    /// position in predicate, positions are fixed after initialization
    pos: usize,
    /// the key for defining special positions for [TypedPredicate]
    key: &'static str
}

impl PredicatePos{
    pub fn new(pos: usize, variable: VarPtr) -> PredicatePos{
        PredicatePos{variable, properties: 0, pos, key: ""}
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

    fn clone_from(&mut self, source: &Self) {
        *self = source.clone();
    }
}

impl From<&VarPtr> for Binding {
    fn from(value: &VarPtr) -> Self {
        Binding::Variable(value.clone())
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
    };
}

binding_operator!(Add, add, "+");
binding_operator!(Mul, mul, "*");
binding_operator!(Div, div, "/");
binding_operator!(Sub, sub, "-");

/// A predicate with bound positions
#[derive(Debug)]
struct BoundPredicate {
    /// The predicate to be used
    predicate: PredicatePtr,
    /// define bindings for some position of the predicate
    bindings: Vec<Binding>
}

impl BoundPredicate {
    fn new(predicate: PredicatePtr, bindings: Vec<Binding>) -> BoundPredicate {
        BoundPredicate{predicate, bindings}
    }

    fn nemo_string(&self, var_names: &mut VariableTranslator, state: &mut GenState) -> String {
        let inner = self.bindings.iter()
            .map(|b| b.nemo_string(var_names))
            .collect::<Vec<_>>()
            .join(", ");
        let predicate_name = self.predicate.construct_program(state);
        format!("{predicate_name}({inner})")
    }
}

/// A NEMO rule
/// rules are always stored in [Predicate] instances
#[derive(Debug)]
struct Rule {
    /// bindings in predicate that has this rule as definition
    bindings: Vec<Binding>,
    /// rule body
    body: Vec<BoundPredicate>
}

impl Rule {
    fn new(bindings: Vec<Binding>, body: Vec<BoundPredicate>) -> Rule{
        Rule{bindings, body}
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
        let head_inner = self.bindings.iter()
            .map(|b| b.nemo_string(&mut var_names))
            .collect::<Vec<_>>()
            .join(", ");
        let body = self.body.iter()
            .map(|a| a.nemo_string(&mut var_names, state))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{predicate_name}({head_inner}) :- {body} .")
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
            self.bindings.join(", ")
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
                .enumerate()
                .map(|(i, v)| PredicatePos::new(i, v.clone()))
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
    pub fn name(&self, predicate: &PredicatePtr) -> Option<String>{
        self.already_generated_predicates.get(predicate).cloned()
    }

    /// determine if the predicate is registered
    pub fn has(&self, predicate: &PredicatePtr) -> bool {
        self.already_generated_predicates.contains_key(predicate)
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

    /// See also [Predicate::property_at]
    pub fn property_at(&self, property: u32, pos: usize) -> bool {
        let p = self.ptr.borrow();
        p.property_at(property, pos)
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
}

pub fn add_fact(p: &dyn TypedPredicate, fact: Fact){
    p.get_predicate().add_fact(fact)
}

pub fn add_rule(p: &dyn TypedPredicate, rule: Rule){
    p.get_predicate().add_rule(rule)
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
            ProtoBinding::VariableSet(s) => panic!("VariableSet \"{s}\" not resolved."),
            ProtoBinding::RenameSet(s) => panic!("RenameSet \"{s}\" not resolved."),
        }
    }
}

#[derive(Debug)]
pub enum ProtoPredicate {
    Explicit(PredicatePtr, Vec<ProtoBinding>),
}

impl ProtoPredicate {
    fn compile(
        self,
        variables: &mut HashMap<String, VarPtr>,
        predicates: &mut Vec<BoundPredicate>
    ) {
        match self {
            ProtoPredicate::Explicit(predicate, bindings) => {
                predicates.push(
                    BoundPredicate::new(
                        predicate.clone(),
                        bindings.into_iter()
                            .enumerate()
                            .map(|(i, b)| b.to_binding(
                                Some(predicate.var_at(i)), variables
                            ))
                            .collect()
                    )
                )
            }
        }
    }
}

fn binding_parts<'a, 'b>(proto_bindings: &'a Vec<ProtoBinding>, vars: &'b Vec<VarPtr>) -> (&'a [ProtoBinding], &'b [VarPtr], &'a [ProtoBinding]) {
    let mut start_len = 0;
    let mut end_len = 0;
    let mut in_start = true;

    for b in proto_bindings {
        if in_start {
            match b {
                ProtoBinding::Binding(_) | ProtoBinding::NamedConnection(_) => start_len += 1,
                ProtoBinding::VariableSet(_) | ProtoBinding::RenameSet(_) => in_start = false
            }
        } else {
            match b {
                ProtoBinding::Binding(_) | ProtoBinding::NamedConnection(_) => end_len += 1,
                ProtoBinding::VariableSet(_) | ProtoBinding::RenameSet(_) => {
                    if end_len > 0 {panic!("Positional binding only allowed at start and end")}
                }
            }
        }
    }
    let var_strings: Vec<String> = vars.iter().map(|v| v.to_string()).collect();
    assert!(start_len <= vars.len(), "can not bind {} (front) variables to positions [{}]", start_len, var_strings.join(", "));
    assert!(start_len <= (vars.len() - end_len), "{} front and {} back variables are too much for [{}]", start_len, end_len, var_strings.join(", "));

    (
        &proto_bindings[..start_len],
        &vars[start_len..(vars.len() - end_len)],
        &proto_bindings[(proto_bindings.len() - end_len)..]
    )
}

fn hash_dedup(vec: &Vec<VarPtr>) -> Vec<VarPtr>{
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

    pub fn finalize_atom(&mut self, predicate: PredicatePtr){
        let mut new_vec: Vec<ProtoBinding> = Vec::new();
        if let Some(len) = self.expected_len {
            assert_eq!(self.partial_atom.len(), len, "There are bindings missing in the end.");
            self.expected_len = None;
        }
        std::mem::swap(&mut new_vec, &mut self.partial_atom);
        self.body.push(ProtoPredicate::Explicit(predicate, new_vec));
    }

    fn check(&self){
        assert!(self.partial_atom.is_empty(), "partial atom read");
        if let Some(p) = &self.target_predicate {
            assert_eq!(p.label(), self.predicate_name, "name mismatch");
        }
        else {
            assert!(!self.predicate_name.is_empty(), "predicate name not set");
        }
    }

    fn resolve_variable_sets(&self) -> (Vec<ProtoBinding>, Vec<ProtoPredicate>){
        let mut var_predicates: HashMap<VarPtr, u64> = HashMap::new();
        let mut set_predicates: HashMap<String, u64> = HashMap::new();
        let mut predicates_with_rename_set: HashSet<PredicatePtr> = HashSet::new();

        // compute which predicate contains which variables and var set bindings
        // handle head
        if let Some(target) = &self.target_predicate{
            let target_vars = target.vars();
            let (start, middle_vars, end) = binding_parts(&self.head, &target_vars);
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
        for (i, proto_predicate) in self.body.iter().enumerate() {
            let flag: u64 = { 2u64 }.checked_pow((i + 1) as u32).expect("long predicate lists are not supported");
            match proto_predicate {
                ProtoPredicate::Explicit(predicate, bindings) => {
                    // set vars vor this predicate
                    let predicate_vars = predicate.vars();
                    let (start, middle_vars, end) = binding_parts(bindings, &predicate_vars);
                    for var in middle_vars {
                        let current_predicates = *var_predicates.get(var).unwrap_or(&0);
                        var_predicates.insert(var.clone(), current_predicates | flag);
                    }

                    // check for rename set
                    let mut has_rename_set = false;
                    for proto_binding in bindings{
                        match proto_binding {
                            ProtoBinding::RenameSet(_) => {has_rename_set = true},
                            _ => {}
                        }
                    }

                    // set var sets for this predicate
                    if !has_rename_set {
                        for proto_binding in bindings{
                            match proto_binding {
                                ProtoBinding::VariableSet(s) => {
                                    let current_predicates = *set_predicates.get(s).unwrap_or(&0);
                                    set_predicates.insert(s.clone(), current_predicates | flag);
                                }
                                _ => {}
                            }
                        }
                    }
                    else {
                        predicates_with_rename_set.insert(predicate.clone());
                    }
                }
            }
        }
        let set_index: HashMap<_, _> = set_predicates.into_iter().map(|(k, v)| (v, k)).collect();

        // Resolve variable and rename sets in body
        let mut new_body: Vec<ProtoPredicate> = Vec::new();
        let mut set_variables: HashMap<String, Vec<VarPtr>> = HashMap::new();
        for proto_predicate in self.body.iter(){
            match proto_predicate {
                ProtoPredicate::Explicit(predicate, bindings) => {
                    let predicate_vars = predicate.vars();
                    let (start, middle_vars, end) = binding_parts(bindings, &predicate_vars);
                    let mut new_bindings: Vec<ProtoBinding> = Vec::new();
                    new_bindings.extend(start.iter().cloned());
                    for var in middle_vars {
                        let predicates = *var_predicates.get(var).expect("predicates for var not computed.");
                        let matched = set_index.get(&predicates).is_some();
                        let allow_unmatched = predicates_with_rename_set.contains(predicate);
                        if !(matched || allow_unmatched) {panic!("var {var} in {} could not be bound to any var set", predicate.label())}
                        if matched {
                            new_bindings.push(ProtoBinding::Binding(Binding::Variable(var.clone())))
                        }
                        else {
                            new_bindings.push(ProtoBinding::Binding(Binding::Variable(var.distinct_new())))
                        }
                        if let Some(var_set) = set_index.get(&predicates){
                            set_variables.entry(var_set.clone()).or_insert_with(Vec::new).push(var.clone());
                        }
                    }
                    new_bindings.extend(end.iter().cloned());
                    new_body.push(ProtoPredicate::Explicit(predicate.clone(), new_bindings))
                }
            }
        }

        // resolve head
        let mut new_head: Vec<ProtoBinding> = Vec::new();
        if let Some(target) = &self.target_predicate {
            let predicate_vars = target.vars();
            let (start, middle_vars, end) = binding_parts(&self.head, &predicate_vars);
            new_head.extend(start.iter().cloned());
            for var in middle_vars {
                let predicates = *var_predicates.get(var).expect("predicates for var in head not computed.");
                if set_index.get(&predicates).is_some() {
                    new_head.push(ProtoBinding::Binding(Binding::Variable(var.clone())))
                }
                else {
                    panic!("{var} not found in body")
                }
            }
            new_head.extend(end.iter().cloned());
        } else {
            for binding in &self.head {
                match binding {
                    ProtoBinding::Binding(b) =>
                        new_head.push(ProtoBinding::Binding(b.clone())),
                    ProtoBinding::NamedConnection(n) =>
                        new_head.push(ProtoBinding::NamedConnection(n.clone())),
                    ProtoBinding::RenameSet(_) => panic!("rename set in head not allowed"),
                    ProtoBinding::VariableSet(s) => {
                        let vars = set_variables.get(s).expect(&format!("Var set {s} not in body"));
                        for v in hash_dedup(vars) {
                             new_head.push(ProtoBinding::Binding(Binding::Variable(v)))
                        }
                    }
                }
            }
        }

        (new_head, new_body)
    }

    fn to_rule(self) -> Rule {
        let (proto_head, proto_body) = self.resolve_variable_sets();
        let mut name_lookup: HashMap<String, VarPtr> = HashMap::new();
        let mut predicates: Vec<BoundPredicate> = Vec::new();


        for proto_predicate in proto_body{
            proto_predicate.compile(&mut name_lookup, &mut predicates)
        }

        let mut head: Vec<Binding> = Vec::new();
        for proto_binding in proto_head {
            head.push(proto_binding.to_binding(None, &mut name_lookup))
        }

        Rule::new(head, predicates)
    }

    pub fn to_predicate<T: TypedPredicate>(self) -> T {
        self.check();
        let name = self.predicate_name.clone();
        let rule = self.to_rule();

        let mut result = T::create(
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
        let mut $name = crate::nemo_model::Basic::create(stringify!($name), vec![$($arg),*]);
    };
    ($name:ident($($arg:ident),*); $type:ty) => {
        let mut $name = <$type>::create(stringify!($name), vec![$($arg),*]);
    };
}

macro_rules! nemo_def {
    ( // pattern duplicated for nemo_add but without type
        $head_name:ident(
            $(
                $(
                    @$head_key_front:ident:
                        $(?$head_connection_name_front:ident)?
                        $($head_expression_front:expr)?
                ),+;
            )?

            $(
                $(??$head_var_set:ident)?
                $(?$head_connection_name:ident)?
                $($head_expression:expr)?
            ),*

            $(
                ;$(
                    @$head_key_back:ident:
                        $(?$head_connection_name_back:ident)?
                        $($head_expression_back:expr)?
                ),+
            )?

        ) :- $(
            $(
                $body_predicate:ident(
                    $(
                        $(
                            @$body_key_front:ident:
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
                            @$body_key_back:ident:
                                $(?$body_connection_name_back:ident)?
                                $($body_expression_back:expr)?
                        ),+
                    )?
                )
            )?
            $($body_filter:block)?
        ),+; $predicate_type:ty
    ) => {
        let mut builder = crate::nemo_model::RuleBuilder::new();
        let head_predicate = <$predicate_type>::create_dummy();
        /*
        This block is duplicated also at nemo_add.

        The reason for this is that IDE support when calling nested macros is limited.
        ----- DUPLICATED BLOCK -----
         */
        builder.set_property_name(stringify!($head_name));

        // HEAD
        // head-front
        $(
            $(
                head_predicate.$head_key_front(
                    &mut builder,
                    $(
                        crate::nemo_model::ProtoBinding::NamedConnection(
                            stringify!($head_connection_name_front).to_string()
                        )
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::Binding(
                            crate::nemo_model::Binding::from(&$head_expression_front)
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
                    crate::nemo_model::ProtoBinding::Binding(
                        crate::nemo_model::Binding::from(&$head_expression)
                    )
                )?
            );
        )*

        // head-back
        $(
            $(
                head_predicate.$head_key_back(
                    &mut builder,
                    $(
                        crate::nemo_model::ProtoBinding::NamedConnection(
                            stringify!($head_connection_name_back).to_string()
                        )
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::Binding(
                            crate::nemo_model::Binding::from(&$head_expression_back)
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
                        {&$body_predicate}.$body_key_front(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($body_connection_name_front).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::Binding(
                                    crate::nemo_model::Binding::from(&$body_expression_front)
                                )
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
                            crate::nemo_model::ProtoBinding::Binding(
                                crate::nemo_model::Binding::from(&$body_expression)
                            )
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
                        {&$body_predicate}.$body_key_back(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($body_connection_name_back).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::Binding(
                                    crate::nemo_model::Binding::from(&$body_expression_back)
                                )
                            )?
                        );
                    )+
                )?

                builder.finalize_atom({&$body_predicate}.get_predicate());
            )?

            // body filters
            // comming soon
        )+
        /*
        ----- END OF DUPLICATED BLOCK -----
         */

        let mut $head_name = builder.to_predicate::<$predicate_type>();
    };
}

macro_rules! nemo_add {
    ($name:ident($($arg:expr),*) .) => {
        crate::nemo_model::add_fact(&$name,
            crate::nemo_model::Fact::new(vec![$({$arg}.to_string()),*])
        )
    };
    ( // pattern duplicated for nemo_def but with type
        $head_name:ident(
            $(
                $(
                    @$head_key_front:ident:
                        $(?$head_connection_name_front:ident)?
                        $($head_expression_front:expr)?
                ),+;
            )?

            $(
                $(??$head_var_set:ident)?
                $(?$head_connection_name:ident)?
                $($head_expression:expr)?
            ),*

            $(
                ;$(
                    @$head_key_back:ident:
                        $(?$head_connection_name_back:ident)?
                        $($head_expression_back:expr)?
                ),+
            )?

        ) :- $(
            $(
                $body_predicate:ident(
                    $(
                        $(
                            @$body_key_front:ident:
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
                            @$body_key_back:ident:
                                $(?$body_connection_name_back:ident)?
                                $($body_expression_back:expr)?
                        ),+
                    )?
                )
            )?
            $($body_filter:block)?
        ),+
    ) => {
        let mut builder = crate::nemo_model::RuleBuilder::new_for({&$head_name}.get_predicate());
        let head_predicate = {&$head_name};
        /*
        This block is duplicated also at nemo_def.

        The reason for this is that IDE support when calling nested macros is limited.
        ----- DUPLICATED BLOCK -----
         */
        builder.set_property_name(stringify!($head_name));

        // HEAD
        // head-front
        $(
            $(
                head_predicate.$head_key_front(
                    &mut builder,
                    $(
                        crate::nemo_model::ProtoBinding::NamedConnection(
                            stringify!($head_connection_name_front).to_string()
                        )
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::Binding(
                            Binding::from($head_expression_front)
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
                    crate::nemo_model::ProtoBinding::Binding(
                        Binding::from($head_expression)
                    )
                )?
            );
        )*

        // head-back
        $(
            $(
                head_predicate.$head_key_back(
                    &mut builder,
                    $(
                        crate::nemo_model::ProtoBinding::NamedConnection(
                            stringify!($head_connection_name_back).to_string()
                        )
                    )?
                    $(
                        crate::nemo_model::ProtoBinding::Binding(
                            Binding::from($head_expression_back)
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
                        {&$body_predicate}.$body_key_front(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($body_connection_name_front).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::Binding(
                                    Binding::from($body_expression_front)
                                )
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
                            crate::nemo_model::ProtoBinding::Binding(
                                Binding::from($body_expression)
                            )
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
                        {&$body_predicate}.$body_key_back(
                            &mut builder,
                            $(
                                crate::nemo_model::ProtoBinding::NamedConnection(
                                    stringify!($body_connection_name_back).to_string()
                                )
                            )?
                            $(
                                crate::nemo_model::ProtoBinding::Binding(
                                    Binding::from($body_expression_back)
                                )
                            )?
                        );
                    )+
                )?

                builder.finalize_atom({&$body_predicate}.get_predicate());
            )?

            // body filters
            // comming soon
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
pub(crate) use nemo_call;


//TODOS:
// - Filters
// - Aggregates
// - existential rules
// - negation
