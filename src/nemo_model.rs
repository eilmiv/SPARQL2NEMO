use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::Add;
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
    /// the key for defining special positions for [PredicateType]
    key: &'static str
}

impl PredicatePos{
    pub fn new(pos: usize, variable: VarPtr) -> PredicatePos{
        PredicatePos{variable, properties: 0, pos, key: ""}
    }
}

/// A binding of a predicate position in a [Rule]
#[derive(Debug)]
enum Binding {
    Constant(String),
    Variable(VarPtr),
    Existential(VarPtr),
}

impl Binding {
    fn nemo_string(&self, var_names: &mut VariableTranslator) -> String {
        match self {
            Binding::Constant(s) => s.clone(),
            Binding::Variable(v) => format!("?{}", var_names.get(v.clone())),
            Binding::Existential(v) => format!("!{}", var_names.get(v.clone())),
        }
    }

    fn variable(&self) -> VarPtr {
        match self {
            Binding::Constant(_) => VarPtr::new("VAR"),
            Binding::Variable(v) => v.clone(),
            Binding::Existential(v) => v.clone(),
        }
    }
}

impl From<VarPtr> for Binding {
    fn from(value: VarPtr) -> Self {
        Binding::Variable(value)
    }
}

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

        let new_name = self.names.get(variable.label());
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

pub trait TypedPredicate: Debug{
    /// an implementation may want to replace some of the variables with new custom variables
    fn create(label: &str, variables: Vec<VarPtr>) -> Self where Self: Sized;
    fn get_predicate(&self) -> PredicatePtr;
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

    fn get_predicate(&self) -> PredicatePtr {
        self.inner.clone()
    }
}


pub enum ProtoBinding {
    Binding(Binding),
    NamedConnection(String),
}

impl ProtoBinding {
    fn to_binding(self, default_var: Option<VarPtr>, variables: &mut HashMap<String, VarPtr>) -> Binding {
        match self {
            ProtoBinding::Binding(b) => b,
            ProtoBinding::NamedConnection(name) => {
                match variables.get(&name) {
                    Some(v) => Binding::Variable(v.clone()),
                    None => {
                        let var = default_var.expect("Variable has to be bound");
                        variables.insert(name.clone(), var.clone());
                        Binding::Variable(var)
                    }
                }
            },
        }
    }
}

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


pub struct RuleBuilder {
    predicate_name: String,
    head: Vec<ProtoBinding>,
    body: Vec<ProtoPredicate>,
    partial_atom: Vec<ProtoBinding>,
    target_predicate: Option<PredicatePtr>,
}

impl RuleBuilder {
    pub fn new() -> RuleBuilder {
        RuleBuilder{
            predicate_name: String::new(),
            head: Vec::new(),
            body: Vec::new(),
            partial_atom: Vec::new(),
            target_predicate: None
        }
    }

    pub fn new_for(predicate: PredicatePtr) -> RuleBuilder{
        let mut result = RuleBuilder::new();
        result.target_predicate = Some(predicate);
        result
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

    pub fn finalize_atom(&mut self, predicate: PredicatePtr){
        let mut new_vec: Vec<ProtoBinding> = Vec::new();
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

    fn to_rule(self) -> Rule {
        let RuleBuilder{head: proto_head, body: proto_body, .. } = self;
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
    (
        $head_name:ident(
            $(?$head_connection_name:ident),*
        ) :- $(
            $body_predicate:ident(
                $(?$body_connection_name:ident),*
            )
        ),+; $predicate_type:ty
    ) => {
        let mut builder = crate::nemo_model::RuleBuilder::new();
        builder.set_property_name(stringify!($head_name));

        $(
            builder.add_head_binding(
                crate::nemo_model::ProtoBinding::NamedConnection(
                    stringify!($head_connection_name).to_string()
                )
            );
        )*

        $(
            $(
                builder.add_body_binding(
                    crate::nemo_model::ProtoBinding::NamedConnection(
                        stringify!($body_connection_name).to_string()
                    )
                );
            )*
            builder.finalize_atom({&$body_predicate}.get_predicate());
        )+

        let mut $head_name = builder.to_predicate::<$predicate_type>();
    };
}

macro_rules! nemo_add {
    ($name:ident($($arg:expr),*) .) => {
        crate::nemo_model::add_fact(&$name,
            crate::nemo_model::Fact::new(vec![$({$arg}.to_string()),*])
        )
    };
    (
        $head_name:ident(
            $(?$head_connection_name:ident),*
        ) :- $(
            $body_predicate:ident(
                $(?$body_connection_name:ident),*
            )
        ),+
    ) => {
        let mut builder = crate::nemo_model::RuleBuilder::new_for({&$head_name}.get_predicate());
        builder.set_property_name(stringify!($head_name));

        $(
            builder.add_head_binding(
                crate::nemo_model::ProtoBinding::NamedConnection(
                    stringify!($head_connection_name).to_string()
                )
            );
        )*

        $(
            $(
                builder.add_body_binding(
                    crate::nemo_model::ProtoBinding::NamedConnection(
                        stringify!($body_connection_name).to_string()
                    )
                );
            )*
            builder.finalize_atom({&$body_predicate}.get_predicate());
        )+

        builder.perform_add();
    };
}

pub(crate) use nemo_declare;
pub(crate) use nemo_add;
pub(crate) use nemo_def;
