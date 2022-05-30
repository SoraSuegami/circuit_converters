use crate::gates::*;
use std::cell::{Ref, RefCell, RefMut};
use std::collections::HashMap;
use std::marker::PhantomData;
use std::rc::Rc;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum BoolCircuitError {
    #[error("The gate of id {0} is unknown.")]
    UnknownGate(GateId),
    #[error("The module of id {0} is unknown.")]
    UnknownModule(ModuleId),
    #[error("The output of the wire id {0} is unknown.")]
    UnknownOutput(WireId),
    #[error("The depended gate ids for the gate id {0} is unknown.")]
    UnknownDependence(GateId),
    #[error("The input of wire id {0} is fixed.")]
    FixedInput(WireId),
    #[error("There is no valid gate in input gates of the module.")]
    InvalidModuleInputGate,
}

#[derive(Debug, Clone)]
pub struct BoolCircuitRef<G: Gate, C: BoolCircuit<G>>(Rc<RefCell<C>>, PhantomData<G>);

impl<G: Gate, C: BoolCircuit<G>> BoolCircuitRef<G, C> {
    pub fn new(circuit: C) -> Self {
        Self(Rc::new(RefCell::new(circuit)), PhantomData)
    }

    pub fn clone(&self) -> Self {
        Self(Rc::clone(self.inner()), PhantomData)
    }

    pub fn borrow(&self) -> Ref<C> {
        self.inner().borrow()
    }

    pub fn borrow_mut(&mut self) -> RefMut<'_, C> {
        (*self.0).borrow_mut()
    }

    fn inner(&self) -> &Rc<RefCell<C>> {
        &self.0
    }
}
pub trait BoolCircuit<G: Gate>: Sized {
    fn new() -> Self;
    fn to_ref(self) -> BoolCircuitRef<G, Self> {
        BoolCircuitRef::new(self)
    }
    fn input_len(&self) -> usize;
    fn output_len(&self) -> usize;
    fn num_wire(&self) -> usize;
    fn num_gate(&self) -> usize;
    fn depth_whole(&self) -> Result<usize, BoolCircuitError>;
    fn depth_of_output(&self, output_wire_id: &WireId) -> Result<usize, BoolCircuitError>;
    fn input_to_gate_id(&self, wire_id: &WireId) -> Result<&Option<GateId>, BoolCircuitError>;
    fn output_to_gate_id(&self, wire_id: &WireId) -> Result<&GateId, BoolCircuitError>;
    fn get_gate(&self, gate_id: &GateId) -> Result<&NXAOBoolGate, BoolCircuitError>;
    fn get_module(&self, module_id: &ModuleId) -> Result<&NXAOBoolCircuit, BoolCircuitError>;
    fn get_depended_gates(&self, gate_id: &GateId) -> Result<Vec<GateId>, BoolCircuitError>;
    fn input(&mut self) -> Result<GateId, BoolCircuitError>;
    fn output(&mut self, gate_id: GateId) -> Result<WireId, BoolCircuitError>;
    fn not(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn xor(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn and(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn or(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn eq(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn identity(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn register_module(&mut self, module_circuit: Self) -> ModuleId;
    fn module(
        &mut self,
        module_id: &ModuleId,
        gate_ids: &[GateId],
    ) -> Result<Vec<GateId>, BoolCircuitError>;
    fn fix_input(&mut self, wire_id: &WireId, value: bool) -> Result<(), BoolCircuitError>;
    //fn const_bit(&mut self, value: bool) -> Result<GateId, BoolCircuitError>;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NXAOBoolCircuit {
    pub input_map: HashMap<WireId, Option<GateId>>,
    pub output_map: HashMap<WireId, GateId>,
    pub gate_map: HashMap<GateId, NXAOBoolGate>,
    pub module_map: HashMap<ModuleId, Self>,
    pub gate_dependence_map: HashMap<GateId, Vec<GateId>>,
    pub input_len: usize,
    pub output_len: usize,
    pub num_module: usize,
    pub num_wire: usize,
    pub num_gate: usize,
    pub gate_index: usize,
}

impl BoolCircuit<NXAOBoolGate> for NXAOBoolCircuit {
    fn new() -> Self {
        Self {
            input_map: HashMap::new(),
            output_map: HashMap::new(),
            gate_map: HashMap::new(),
            module_map: HashMap::new(),
            gate_dependence_map: HashMap::new(),
            input_len: 0,
            output_len: 0,
            num_module: 0,
            num_wire: 0,
            num_gate: 0,
            gate_index: 0,
        }
    }

    fn input_len(&self) -> usize {
        self.input_len
    }

    fn output_len(&self) -> usize {
        self.output_len
    }

    fn num_wire(&self) -> usize {
        self.num_wire
    }

    fn num_gate(&self) -> usize {
        self.num_gate
    }

    fn depth_whole(&self) -> Result<usize, BoolCircuitError> {
        let mut max: usize = 0;
        for i in 0..self.output_len {
            let wire_id = WireId(i as u64);
            let depth = self.depth_of_output(&wire_id)?;
            if depth > max {
                max = depth;
            }
        }
        Ok(max)
    }

    fn depth_of_output(&self, output_wire_id: &WireId) -> Result<usize, BoolCircuitError> {
        let output_id = self.output_to_gate_id(output_wire_id)?;
        let gate: &NXAOBoolGate = self.get_gate(&output_id)?;
        Ok(gate.depth())
    }

    fn input_to_gate_id(&self, wire_id: &WireId) -> Result<&Option<GateId>, BoolCircuitError> {
        self.input_map
            .get(wire_id)
            .ok_or(BoolCircuitError::UnknownOutput(*wire_id))
    }

    fn output_to_gate_id(&self, wire_id: &WireId) -> Result<&GateId, BoolCircuitError> {
        self.output_map
            .get(wire_id)
            .ok_or(BoolCircuitError::UnknownOutput(*wire_id))
    }

    fn get_gate(&self, gate_id: &GateId) -> Result<&NXAOBoolGate, BoolCircuitError> {
        self.gate_map
            .get(gate_id)
            .ok_or(BoolCircuitError::UnknownGate(*gate_id))
    }

    fn get_module(&self, module_id: &ModuleId) -> Result<&NXAOBoolCircuit, BoolCircuitError> {
        self.module_map
            .get(module_id)
            .ok_or(BoolCircuitError::UnknownModule(*module_id))
    }

    fn get_depended_gates(&self, gate_id: &GateId) -> Result<Vec<GateId>, BoolCircuitError> {
        let ids = self.gate_dependence_map.get(gate_id);
        if ids.is_none() {
            Ok(Vec::new())
        } else {
            Ok(self.gate_dependence_map[gate_id].to_vec())
        }
    }

    fn input(&mut self) -> Result<GateId, BoolCircuitError> {
        let new_wire_id = WireId(self.input_len as u64);
        let input_gate = InputGate {
            wire_id: new_wire_id,
            is_fixed: false
        };
        self.input_len += 1;
        let new_gate_id = self.add_gate(NXAOBoolGate::Input(input_gate));
        self.input_map.insert(input_gate.wire_id, Some(new_gate_id));
        Ok(new_gate_id)
    }

    fn output(&mut self, gate_id: GateId) -> Result<WireId, BoolCircuitError> {
        if self.gate_map.get(&gate_id).is_none() {
            return Err(BoolCircuitError::UnknownGate(gate_id));
        }
        let new_wire_id = WireId(self.output_len as u64);
        self.output_map.insert(new_wire_id, gate_id);
        self.output_len += 1;
        Ok(new_wire_id)
    }

    fn not(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let input_gate = self.get_gate(gate_id)?;
        let not_gate = NotGate {
            id: *gate_id,
            depth: input_gate.depth() + 1,
        };
        let new_gate_id = self.add_gate(NXAOBoolGate::Not(not_gate));
        self.add_dependence(gate_id, &new_gate_id)?;
        self.num_gate += 1;
        Ok(new_gate_id)
    }

    fn xor(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let input_l_gate = self.get_gate(gate_l_id)?;
        let input_r_gate = self.get_gate(gate_r_id)?;
        let new_depth = if input_l_gate.depth() >= input_r_gate.depth() {
            input_l_gate.depth() + 1
        } else {
            input_r_gate.depth() + 1
        };
        let xor_gate = XorGate {
            left_id: *gate_l_id,
            right_id: *gate_r_id,
            depth: new_depth,
        };
        let new_gate_id = self.add_gate(NXAOBoolGate::Xor(xor_gate));
        self.add_dependence(gate_l_id, &new_gate_id)?;
        self.add_dependence(gate_r_id, &new_gate_id)?;
        self.num_gate += 1;
        Ok(new_gate_id)
    }

    fn and(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let input_l_gate = self.get_gate(gate_l_id)?;
        let input_r_gate = self.get_gate(gate_r_id)?;
        let new_depth = if input_l_gate.depth() >= input_r_gate.depth() {
            input_l_gate.depth() + 1
        } else {
            input_r_gate.depth() + 1
        };
        let and_gate = AndGate {
            left_id: *gate_l_id,
            right_id: *gate_r_id,
            depth: new_depth,
        };
        let new_gate_id = self.add_gate(NXAOBoolGate::And(and_gate));
        self.add_dependence(gate_l_id, &new_gate_id)?;
        self.add_dependence(gate_r_id, &new_gate_id)?;
        self.num_gate += 1;
        Ok(new_gate_id)
    }

    fn or(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let input_l_gate = self.get_gate(gate_l_id)?;
        let input_r_gate = self.get_gate(gate_r_id)?;
        let new_depth = if input_l_gate.depth() >= input_r_gate.depth() {
            input_l_gate.depth() + 1
        } else {
            input_r_gate.depth() + 1
        };
        let or_gate = OrGate {
            left_id: *gate_l_id,
            right_id: *gate_r_id,
            depth: new_depth,
        };
        let new_gate_id = self.add_gate(NXAOBoolGate::Or(or_gate));
        self.add_dependence(gate_l_id, &new_gate_id)?;
        self.add_dependence(gate_r_id, &new_gate_id)?;
        self.num_gate += 1;
        Ok(new_gate_id)
    }

    fn eq(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let xor = self.xor(gate_l_id, gate_r_id)?;
        self.not(&xor)
    }

    fn identity(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let not1 = self.not(gate_id)?;
        self.not(&not1)
    }

    fn register_module(&mut self, module_circuit: Self) -> ModuleId {
        let module_id = ModuleId(self.num_module as u64);
        self.module_map.insert(module_id, module_circuit);
        self.num_module += 1;
        module_id
    }

    fn module(
        &mut self,
        module_id: &ModuleId,
        gate_ids: &[GateId],
    ) -> Result<Vec<GateId>, BoolCircuitError> {
        let gates = gate_ids
            .into_iter()
            .map(|id| self.get_gate(id))
            .collect::<Result<Vec<_>, _>>()?;
        let max_depth = gates
            .into_iter()
            .map(|g| g.depth())
            .max()
            .ok_or(BoolCircuitError::InvalidModuleInputGate)?;
        let module_circuit = self.get_module(module_id)?;
        let input_len = module_circuit.input_len();
        let output_len = module_circuit.output_len();
        let depth = max_depth + module_circuit.depth_whole()?;
        let num_wire = module_circuit.num_wire();
        let num_gate = module_circuit.num_gate();
        self.num_wire += num_wire - input_len - output_len;
        self.num_gate += num_gate;
        let new_gate_ids = (0..output_len)
            .into_iter()
            .map(|i| {
                let module_gate = ModuleGate {
                    input_len,
                    output_len,
                    input_ids: gate_ids.to_vec(),
                    out_index: i,
                    depth,
                    module_id: *module_id,
                };
                self.add_gate(NXAOBoolGate::Module(module_gate))
            })
            .collect::<Vec<GateId>>();
        for (input_id, self_id) in gate_ids.into_iter().zip(&new_gate_ids) {
            self.add_dependence(input_id, self_id)?;
        }
        Ok(new_gate_ids)
    }

    fn fix_input(&mut self, wire_id: &WireId, value: bool) -> Result<(), BoolCircuitError> {
        let input_gate_id = self.input_to_gate_id(wire_id)?.ok_or(BoolCircuitError::FixedInput(*wire_id))?;
        let new_input_gate = InputGate {
            wire_id: *wire_id,
            is_fixed: true
        };
        self.gate_map.insert(input_gate_id, NXAOBoolGate::Input(new_input_gate));
        self.modify_gate_with_fixed_input(&input_gate_id, value)?;
        self.input_len -= 1;
        self.num_wire -= 1;
        self.input_map.insert(*wire_id, None);
        self.gate_dependence_map.insert(input_gate_id, Vec::new());
        Ok(())
    }

    /*fn const_bit(&mut self, value: bool) -> Result<GateId, BoolCircuitError> {
        let input = self.input()?;
        let input_gate = self.get_gate(&input)?;
        match input_gate {
            NXAOBoolGate::Input(gate) => {
                self.fix_input(&gate.wire_id, value)?;
            },
            _=> {}
        };
        Ok(input)
    }*/
}

impl NXAOBoolCircuit {
    fn add_gate(&mut self, gate: NXAOBoolGate) -> GateId {
        let gate_id = GateId(self.gate_index as u64);
        self.gate_map.insert(gate_id, gate);
        self.gate_index += 1;
        self.num_wire += 1;
        gate_id
    }

    fn add_dependence(
        &mut self,
        input_id: &GateId,
        self_id: &GateId,
    ) -> Result<(), BoolCircuitError> {
        let gate_ids = self.gate_dependence_map.get(input_id);
        if gate_ids.is_none() {
            self.gate_dependence_map.insert(*input_id, vec![*self_id]);
        } else {
            let gate_ids = self
                .gate_dependence_map
                .get_mut(input_id)
                .ok_or(BoolCircuitError::UnknownDependence(*input_id))?;
            gate_ids.push(*self_id);
        }
        Ok(())
    }

    fn modify_gate_with_fixed_input(&mut self, gate_id: &GateId, value: bool) -> Result<(), BoolCircuitError> {
        let depended_gate_ids = self.get_depended_gates(gate_id)?;
        //println!("gate_id {}, depend_ids {:?}",gate_id, depended_gate_ids);
        for id in depended_gate_ids {
            let gate = self.get_gate(&id)?;
            match gate {
                NXAOBoolGate::Input(_) => {},
                NXAOBoolGate::Not(_) => {
                    let not_fixed_bit = !value;
                    self.modify_gate_with_fixed_input(&id, not_fixed_bit)?;
                },
                NXAOBoolGate::Xor(gate) => {
                    let pair_input_gate_id = if gate.left_id == *gate_id {
                        gate.right_id
                    } else {
                        gate.left_id
                    };
                    let pair_input_gate = self.get_gate(&pair_input_gate_id)?;
                    let depth = pair_input_gate.depth()+1;
                    if !value {
                        let not = self.not(&pair_input_gate_id)?;
                        let new_gate = NotGate {
                            id: not,
                            depth: depth
                        };
                        self.gate_map.insert(id, NXAOBoolGate::Not(new_gate));
                    }
                    else {
                        let new_not_gate = NotGate {
                            id: pair_input_gate_id,
                            depth: pair_input_gate.depth()+1
                        };
                        self.gate_map.insert(id, NXAOBoolGate::Not(new_not_gate));
                    }
                },
                NXAOBoolGate::And(gate) => {
                    let pair_input_gate_id = if gate.left_id == *gate_id {
                        gate.right_id
                    } else {
                        gate.left_id
                    };
                    let pair_input_gate = self.get_gate(&pair_input_gate_id)?;
                    let depth = pair_input_gate.depth()+1;
                    if !value {
                        self.num_wire -= 1;
                        let dependence = self.gate_dependence_map.get_mut(&pair_input_gate_id).ok_or(BoolCircuitError::UnknownDependence(pair_input_gate_id))?;
                        for i in 0..dependence.len() {
                            if id == dependence[i] {
                                dependence.remove(i);
                                break;
                            }
                        }
                        self.modify_gate_with_fixed_input(&id, false)?;
                        /*let new_xor_gate = XorGate {
                            left_id: pair_input_gate_id,
                            right_id: pair_input_gate_id,
                            depth: pair_input_gate.depth()+1
                        };
                        self.gate_map.insert(id, NXAOBoolGate::Xor(new_xor_gate));*/
                    }
                    else {
                        let not = self.not(&pair_input_gate_id)?;
                        let new_gate = NotGate {
                            id: not,
                            depth: depth
                        };
                        self.gate_map.insert(id, NXAOBoolGate::Not(new_gate));
                    }
                },
                NXAOBoolGate::Or(gate) => {
                    let pair_input_gate_id = if gate.left_id == *gate_id {
                        gate.right_id
                    } else {
                        gate.left_id
                    };
                    let pair_input_gate = self.get_gate(&pair_input_gate_id)?;
                    let depth = pair_input_gate.depth()+1;
                    if !value {
                        let not = self.not(&pair_input_gate_id)?;
                        let new_gate = NotGate {
                            id: not,
                            depth: depth
                        };
                        self.gate_map.insert(id, NXAOBoolGate::Not(new_gate));
                    }
                    else {
                        self.modify_gate_with_fixed_input(&id, true)?;
                    }
                },
                NXAOBoolGate::Module(_) => {}
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn input1_output1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id = circuit.input().unwrap();
        circuit.output(input_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 1);
        assert_eq!(circuit.output_len(), 1);
        assert_eq!(circuit.depth_whole().unwrap(), 0);
    }

    #[test]
    fn input1_not_ouput1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id = circuit.input().unwrap();
        let not_gate_id = circuit.not(&input_gate_id).unwrap();
        circuit.output(not_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 1);
        assert_eq!(circuit.output_len(), 1);
        assert_eq!(circuit.depth_whole().unwrap(), 1);
    }

    #[test]
    fn input_xor_output1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let or_gate_id = circuit.xor(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(or_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 2);
        assert_eq!(circuit.output_len(), 1);
        assert_eq!(circuit.depth_whole().unwrap(), 1);
    }

    #[test]
    fn input2_and_output1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let and_gate_id = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(and_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 2);
        assert_eq!(circuit.output_len(), 1);
        assert_eq!(circuit.depth_whole().unwrap(), 1);
    }

    #[test]
    fn input2_or_output1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let or_gate_id = circuit.or(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(or_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 2);
        assert_eq!(circuit.output_len(), 1);
        assert_eq!(circuit.depth_whole().unwrap(), 1);
    }

    #[test]
    fn input3_and_or_output1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let input_gate_id3 = circuit.input().unwrap();
        let and_gate_id = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        let or_gate_id = circuit.or(&and_gate_id, &input_gate_id3).unwrap();
        circuit.output(or_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 3);
        assert_eq!(circuit.output_len(), 1);
        assert_eq!(circuit.depth_whole().unwrap(), 2);
    }
}
