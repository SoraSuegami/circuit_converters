use num_traits::Zero;
use std::ops::{Add, AddAssign};
use std::{fmt, hash::Hash};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WireId(pub u64);

impl fmt::Display for WireId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Add for WireId {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        WireId(self.0 + rhs.0)
    }
}

impl AddAssign for WireId {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl Zero for WireId {
    fn zero() -> Self {
        WireId(0)
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GateId(pub u64);

impl fmt::Display for GateId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Add for GateId {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        GateId(self.0 + rhs.0)
    }
}

impl AddAssign for GateId {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl Zero for GateId {
    fn zero() -> Self {
        GateId(0)
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u64);

impl fmt::Display for ModuleId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub trait BooleanElement: Clone + Eq {
    fn to_bits(&self) -> Vec<bool>;
    fn bit_size() -> usize;
}

pub trait Gate: Clone + Eq {
    fn input_len(&self) -> usize;
    fn output_len(&self) -> usize;
    fn input_gate_ids(&self) -> Vec<GateId>;
    fn to_str(&self) -> String;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NXAOBoolGate {
    Input(InputGate),
    Const(ConstGate),
    Not(NotGate),
    And(AndGate),
    Xor(XorGate),
    Or(OrGate),
    Module(ModuleGate),
}

impl Gate for NXAOBoolGate {
    fn input_len(&self) -> usize {
        match self {
            NXAOBoolGate::Input(g) => g.input_len(),
            NXAOBoolGate::Const(g) => g.input_len(),
            NXAOBoolGate::Not(g) => g.input_len(),
            NXAOBoolGate::And(g) => g.input_len(),
            NXAOBoolGate::Xor(g) => g.input_len(),
            NXAOBoolGate::Or(g) => g.input_len(),
            NXAOBoolGate::Module(g) => g.input_len(),
        }
    }
    fn output_len(&self) -> usize {
        match self {
            NXAOBoolGate::Input(g) => g.output_len(),
            NXAOBoolGate::Const(g) => g.output_len(),
            NXAOBoolGate::Not(g) => g.output_len(),
            NXAOBoolGate::And(g) => g.output_len(),
            NXAOBoolGate::Xor(g) => g.output_len(),
            NXAOBoolGate::Or(g) => g.output_len(),
            NXAOBoolGate::Module(g) => g.output_len(),
        }
    }
    fn input_gate_ids(&self) -> Vec<GateId> {
        match self {
            NXAOBoolGate::Input(g) => g.input_gate_ids(),
            NXAOBoolGate::Const(g) => g.input_gate_ids(),
            NXAOBoolGate::Not(g) => g.input_gate_ids(),
            NXAOBoolGate::And(g) => g.input_gate_ids(),
            NXAOBoolGate::Xor(g) => g.input_gate_ids(),
            NXAOBoolGate::Or(g) => g.input_gate_ids(),
            NXAOBoolGate::Module(g) => g.input_gate_ids(),
        }
    }
    fn to_str(&self) -> String {
        match self {
            NXAOBoolGate::Input(g) => g.to_str(),
            NXAOBoolGate::Const(g) => g.to_str(),
            NXAOBoolGate::Not(g) => g.to_str(),
            NXAOBoolGate::And(g) => g.to_str(),
            NXAOBoolGate::Xor(g) => g.to_str(),
            NXAOBoolGate::Or(g) => g.to_str(),
            NXAOBoolGate::Module(g) => g.to_str(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InputGate {
    pub wire_id: WireId,
}

impl Gate for InputGate {
    fn input_len(&self) -> usize {
        0
    }

    fn output_len(&self) -> usize {
        1
    }

    fn input_gate_ids(&self) -> Vec<GateId> {
        vec![]
    }

    fn to_str(&self) -> String {
        "INPUT".to_string()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConstGate {
    pub value: bool,
}

impl Gate for ConstGate {
    fn input_len(&self) -> usize {
        0
    }

    fn output_len(&self) -> usize {
        1
    }

    fn input_gate_ids(&self) -> Vec<GateId> {
        vec![]
    }

    fn to_str(&self) -> String {
        "CONST".to_string()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NotGate {
    pub id: GateId,
}

impl Gate for NotGate {
    fn input_len(&self) -> usize {
        1
    }

    fn output_len(&self) -> usize {
        1
    }

    fn input_gate_ids(&self) -> Vec<GateId> {
        vec![self.id]
    }

    fn to_str(&self) -> String {
        "INV".to_string()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct XorGate {
    pub left_id: GateId,
    pub right_id: GateId,
}

impl Gate for XorGate {
    fn input_len(&self) -> usize {
        2
    }

    fn output_len(&self) -> usize {
        1
    }

    fn input_gate_ids(&self) -> Vec<GateId> {
        vec![self.left_id, self.right_id]
    }

    fn to_str(&self) -> String {
        "XOR".to_string()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AndGate {
    pub left_id: GateId,
    pub right_id: GateId,
}

impl Gate for AndGate {
    fn input_len(&self) -> usize {
        2
    }

    fn output_len(&self) -> usize {
        1
    }

    fn input_gate_ids(&self) -> Vec<GateId> {
        vec![self.left_id, self.right_id]
    }

    fn to_str(&self) -> String {
        "AND".to_string()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrGate {
    pub left_id: GateId,
    pub right_id: GateId,
}

impl Gate for OrGate {
    fn input_len(&self) -> usize {
        2
    }

    fn output_len(&self) -> usize {
        1
    }

    fn input_gate_ids(&self) -> Vec<GateId> {
        vec![self.left_id, self.right_id]
    }

    fn to_str(&self) -> String {
        "OR".to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGate {
    pub input_len: usize,
    pub output_len: usize,
    pub input_ids: Vec<GateId>,
    pub out_index: usize,
    pub module_id: ModuleId,
}

impl Gate for ModuleGate {
    fn input_len(&self) -> usize {
        self.input_len
    }

    fn output_len(&self) -> usize {
        self.output_len
    }

    fn input_gate_ids(&self) -> Vec<GateId> {
        self.input_ids.to_vec()
    }

    fn to_str(&self) -> String {
        "MODULE".to_string()
    }
}
