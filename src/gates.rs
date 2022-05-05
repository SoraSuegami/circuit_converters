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
    fn depth(&self) -> usize;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NXAOBoolGate {
    Input(InputGate),
    Not(NotGate),
    And(AndGate),
    Xor(XorGate),
    Or(OrGate),
    //Const(ConstGate),
    Module(ModuleGate),
}

impl Gate for NXAOBoolGate {
    fn input_len(&self) -> usize {
        match self {
            NXAOBoolGate::Input(g) => g.input_len(),
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
            NXAOBoolGate::Not(g) => g.input_gate_ids(),
            NXAOBoolGate::And(g) => g.input_gate_ids(),
            NXAOBoolGate::Xor(g) => g.input_gate_ids(),
            NXAOBoolGate::Or(g) => g.input_gate_ids(),
            NXAOBoolGate::Module(g) => g.input_gate_ids(),
        }
    }
    fn depth(&self) -> usize {
        match self {
            NXAOBoolGate::Input(g) => g.depth(),
            NXAOBoolGate::Not(g) => g.depth(),
            NXAOBoolGate::And(g) => g.depth(),
            NXAOBoolGate::Xor(g) => g.depth(),
            NXAOBoolGate::Or(g) => g.depth(),
            NXAOBoolGate::Module(g) => g.depth(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InputGate {
    pub wire_id: WireId,
    pub value: Option<bool>,
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

    fn depth(&self) -> usize {
        0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NotGate {
    pub id: GateId,
    pub depth: usize,
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

    fn depth(&self) -> usize {
        self.depth
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct XorGate {
    pub left_id: GateId,
    pub right_id: GateId,
    pub depth: usize,
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

    fn depth(&self) -> usize {
        self.depth
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AndGate {
    pub left_id: GateId,
    pub right_id: GateId,
    pub depth: usize,
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

    fn depth(&self) -> usize {
        self.depth
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrGate {
    pub left_id: GateId,
    pub right_id: GateId,
    pub depth: usize,
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

    fn depth(&self) -> usize {
        self.depth
    }
}

/*#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConstGate {
    pub value: bool,
    pub depth: usize,
}

impl Gate for ConstGate {
    fn input_len(&self) -> usize {
        1
    }

    fn output_len(&self) -> usize {
        1
    }

    fn input_gate_ids(&self) -> Vec<GateId> {
        vec![]
    }

    fn depth(&self) -> usize {
        self.depth
    }
}*/

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGate {
    pub input_len: usize,
    pub output_len: usize,
    pub input_ids: Vec<GateId>,
    pub out_index: usize,
    pub depth: usize,
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

    fn depth(&self) -> usize {
        self.depth
    }
}
