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
    #[error("The input of the wire id {0} is unknown.")]
    UnknownInput(WireId),
    #[error("The output of the wire id {0} is unknown.")]
    UnknownOutput(WireId),
    #[error("The depended gate ids for the gate id {0} is unknown.")]
    UnknownDependence(GateId),
    #[error("The input of wire id {0} is fixed.")]
    FixedInput(WireId),
    #[error("The gate of id {0} is not constant gate")]
    NotConstGate(GateId),
    #[error("The gate of id {0} is not module gate")]
    NotModuleGate(GateId),
    #[error("The input gate of id {0} is not found in the module of id {1}")]
    UnknownInputOfModule(GateId, ModuleId),
    #[error("There is no valid gate in input gates of the module.")]
    InvalidModuleInputGate,
}

pub trait BoolCircuit<G: Gate>: Sized + Clone + PartialEq + Eq {
    //fn new() -> Self;
    fn to_ref(self) -> BoolCircuitRef<G, Self>;
    fn input_len(&self) -> usize;
    fn output_len(&self) -> usize;
    fn num_wire(&self) -> usize;
    fn num_gate(&self) -> usize;
    fn num_const(&self) -> usize;
    fn input_to_gate_id(&self, wire_id: &WireId) -> Result<Option<GateId>, BoolCircuitError>;
    fn output_to_gate_id(&self, wire_id: &WireId) -> Result<GateId, BoolCircuitError>;
    fn get_gate(&self, gate_id: &GateId) -> Result<G, BoolCircuitError>;
    fn get_module(&self, module_id: &ModuleId)
        -> Result<BoolCircuitRef<G, Self>, BoolCircuitError>;
    fn get_depended_gates(&self, gate_id: &GateId) -> Result<Vec<GateId>, BoolCircuitError>;
    fn get_const_gates(&self) -> Vec<GateId>;
    fn input(&mut self) -> Result<GateId, BoolCircuitError>;
    fn output(&mut self, gate_id: GateId) -> Result<WireId, BoolCircuitError>;
    fn constant(&mut self, value: bool) -> Result<GateId, BoolCircuitError>;
    fn not(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn xor(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn and(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn or(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn equivalent(
        &mut self,
        gate_l_id: &GateId,
        gate_r_id: &GateId,
    ) -> Result<GateId, BoolCircuitError>;
    fn identity(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError>;
    fn register_module(&mut self, module_circuit: &BoolCircuitRef<G, Self>) -> ModuleId;
    fn sub_circuit(&mut self) -> (ModuleId, BoolCircuitRef<G, Self>);
    fn module(
        &mut self,
        module_id: &ModuleId,
        gate_ids: &[GateId],
    ) -> Result<Vec<GateId>, BoolCircuitError>;
    /*fn modify_with_const_gates(
        &mut self,
        other_const_gate_ids: &[(GateId, bool)],
    ) -> Result<(), BoolCircuitError>;*/
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolCircuitRef<G: Gate, C: BoolCircuit<G>>(Rc<RefCell<C>>, PhantomData<G>);

impl<G: Gate, C: BoolCircuit<G>> BoolCircuitRef<G, C> {
    pub fn new(circuit: C) -> Self {
        let ref_c = RefCell::new(circuit);
        Self(Rc::new(ref_c), PhantomData)
    }

    pub fn clone(&self) -> Self {
        Self(Rc::clone(self.inner()), PhantomData)
    }

    pub fn borrow(&self) -> Ref<C> {
        self.inner().borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<'_, C> {
        (*self.0).borrow_mut()
    }

    pub fn input_len(&self) -> usize {
        self.borrow().input_len()
    }

    pub fn output_len(&self) -> usize {
        self.borrow().output_len()
    }

    pub fn num_wire(&self) -> usize {
        self.borrow().num_wire()
    }

    pub fn num_gate(&self) -> usize {
        self.borrow().num_gate()
    }

    pub fn num_const(&self) -> usize {
        self.borrow().num_const()
    }

    pub fn input_to_gate_id(&self, wire_id: &WireId) -> Result<Option<GateId>, BoolCircuitError> {
        self.borrow().input_to_gate_id(wire_id)
    }

    pub fn output_to_gate_id(&self, wire_id: &WireId) -> Result<GateId, BoolCircuitError> {
        self.borrow().output_to_gate_id(wire_id)
    }

    pub fn get_gate(&self, gate_id: &GateId) -> Result<G, BoolCircuitError> {
        self.borrow().get_gate(gate_id)
    }

    pub fn get_module(&self, module_id: &ModuleId) -> Result<Self, BoolCircuitError> {
        self.borrow().get_module(module_id)
    }

    pub fn get_depended_gates(&self, gate_id: &GateId) -> Result<Vec<GateId>, BoolCircuitError> {
        self.borrow().get_depended_gates(gate_id)
    }

    pub fn get_const_gates(&self) -> Vec<GateId> {
        self.borrow().get_const_gates()
    }

    pub fn input(&mut self) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().input()
    }

    pub fn output(&mut self, gate_id: GateId) -> Result<WireId, BoolCircuitError> {
        self.borrow_mut().output(gate_id)
    }

    pub fn constant(&mut self, value: bool) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().constant(value)
    }

    pub fn not(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().not(gate_id)
    }

    pub fn xor(
        &mut self,
        gate_l_id: &GateId,
        gate_r_id: &GateId,
    ) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().xor(gate_l_id, gate_r_id)
    }

    pub fn and(
        &mut self,
        gate_l_id: &GateId,
        gate_r_id: &GateId,
    ) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().and(gate_l_id, gate_r_id)
    }

    pub fn or(
        &mut self,
        gate_l_id: &GateId,
        gate_r_id: &GateId,
    ) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().or(gate_l_id, gate_r_id)
    }

    pub fn equivalent(
        &mut self,
        gate_l_id: &GateId,
        gate_r_id: &GateId,
    ) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().equivalent(gate_l_id, gate_r_id)
    }

    pub fn identity(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().identity(gate_id)
    }

    pub fn register_module(&mut self, module_circuit: &Self) -> ModuleId {
        self.borrow_mut().register_module(module_circuit)
    }

    pub fn sub_circuit(&mut self) -> (ModuleId, Self) {
        self.borrow_mut().sub_circuit()
    }

    pub fn module(
        &mut self,
        module_id: &ModuleId,
        gate_ids: &[GateId],
    ) -> Result<Vec<GateId>, BoolCircuitError> {
        self.borrow_mut().module(module_id, gate_ids)
    }

    /*pub fn modify_with_const_gates(&mut self) -> Result<(), BoolCircuitError> {
        let mut const_gate_ids = Vec::new();
        for (w_id, _, value) in (&self.1).borrow().iter() {
            let gate_id = self
                .borrow()
                .input_to_gate_id(&w_id)?
                .ok_or(BoolCircuitError::UnknownInput(*w_id))?;
            const_gate_ids.push((gate_id, *value));
        }
        self.borrow_mut()
            .modify_with_const_gates(&const_gate_ids[..])
    }*/

    fn inner(&self) -> &Rc<RefCell<C>> {
        &self.0
    }
}

/*
impl<G: Gate, C: BoolCircuit<G>> BoolCircuit<G> for BoolCircuitRef<G, C> {
    fn input_len(&self) -> usize {
        self.borrow().input_len()
    }

    fn output_len(&self) -> usize {
        self.borrow().output_len()
    }

    fn num_wire(&self) -> usize {
        self.borrow().num_wire()
    }

    fn num_gate(&self) -> usize {
        self.borrow().num_gate()
    }

    fn input_to_gate_id(&self, wire_id: &WireId) -> Result<Option<GateId>, BoolCircuitError> {
        self.borrow().input_to_gate_id(wire_id)
    }

    fn output_to_gate_id(&self, wire_id: &WireId) -> Result<GateId, BoolCircuitError> {
        self.borrow().output_to_gate_id(wire_id)
    }

    fn get_gate(&self, gate_id: &GateId) -> Result<NXAOBoolGate, BoolCircuitError> {
        self.borrow().get_gate(gate_id)
    }

    fn get_module(&self, module_id: &ModuleId) -> Result<BoolCircuitRef<G,Self>, BoolCircuitError> {
        self.borrow().get_module(module_id)
    }

    fn get_depended_gates(&self, gate_id: &GateId) -> Result<Vec<GateId>, BoolCircuitError> {
        self.borrow().get_depended_gates(gate_id)
    }

    fn input(&mut self) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().input()
    }

    fn output(&mut self, gate_id: GateId) -> Result<WireId, BoolCircuitError> {
        self.borrow_mut().output(gate_id)
    }

    fn constant(&mut self, value: bool) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().constant(value)
    }

    fn not(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().not(gate_id)
    }

    fn xor(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().xor(gate_l_id, gate_r_id)
    }

    fn and(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().and(gate_l_id, gate_r_id)
    }

    fn or(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().or(gate_l_id, gate_r_id)
    }

    fn eq(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().eq(gate_l_id, gate_r_id)
    }

    fn identity(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError> {
        self.borrow_mut().identity(gate_id)
    }

    fn register_module(&mut self, module_circuit: Self) -> ModuleId {
        let module_c: C = module_circuit.borrow().clone();
        self.borrow_mut().register_module(module_c)
    }

    fn sub_circuit(&mut self) -> (ModuleId, BoolCircuitRef<NXAOBoolGate,Self>) {
        self.borrow_mut().sub_circuit()
    }

    fn module(
        &mut self,
        module_id: &ModuleId,
        gate_ids: &[GateId],
    ) -> Result<Vec<GateId>, BoolCircuitError> {
        self.borrow_mut().module(module_id, gate_ids)
    }

    fn modify_with_const_gates(&mut self) -> Result<(), BoolCircuitError> {
        self.borrow_mut().modify_with_const_gates()
    }
}
*/

#[derive(Debug, Clone)]
pub struct ModuleStorageRef<G: Gate, C: BoolCircuit<G>>(Rc<RefCell<ModuleStorage<G, C>>>);

impl<G: Gate, C: BoolCircuit<G>> ModuleStorageRef<G, C> {
    pub fn new() -> Self {
        Self(Rc::new(RefCell::new(ModuleStorage::<G, C>::new())))
    }

    pub fn clone(&self) -> Self {
        Self(Rc::clone(self.inner()))
    }

    pub fn borrow(&self) -> Ref<ModuleStorage<G, C>> {
        self.inner().borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<'_, ModuleStorage<G, C>> {
        (*self.0).borrow_mut()
    }

    pub fn get_module(
        &self,
        module_id: &ModuleId,
    ) -> Result<BoolCircuitRef<G, C>, BoolCircuitError> {
        self.borrow().get_module(module_id)
    }

    pub fn register_module(&mut self, module_circuit: &BoolCircuitRef<G, C>) -> ModuleId {
        self.borrow_mut().register_module(module_circuit)
    }

    pub fn num_module(&self) -> usize {
        self.borrow().num_module()
    }

    fn inner(&self) -> &Rc<RefCell<ModuleStorage<G, C>>> {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub struct ModuleStorage<G: Gate, C: BoolCircuit<G>> {
    pub module_map: HashMap<ModuleId, BoolCircuitRef<G, C>>,
    pub num_module: usize,
    pub fix_input_map: HashMap<ModuleId, (ModuleId, Vec<(WireId, G)>)>,
    _g: PhantomData<G>,
}

impl<G: Gate, C: BoolCircuit<G>> ModuleStorage<G, C> {
    pub fn new() -> Self {
        let module_map = HashMap::new();
        let num_module = 0;
        let fix_input_map = HashMap::new();
        Self {
            module_map,
            num_module,
            fix_input_map,
            _g: PhantomData,
        }
    }

    pub fn get_module(
        &self,
        module_id: &ModuleId,
    ) -> Result<BoolCircuitRef<G, C>, BoolCircuitError> {
        self.module_map
            .get(module_id)
            .ok_or(BoolCircuitError::UnknownModule(*module_id))
            .and_then(|c| Ok(c.clone()))
    }

    pub fn register_module(&mut self, module_circuit: &BoolCircuitRef<G, C>) -> ModuleId {
        let module_id = ModuleId(self.num_module as u64);
        self.module_map.insert(module_id, module_circuit.clone());
        self.num_module += 1;
        module_id
    }

    pub fn num_module(&self) -> usize {
        self.num_module
    }
}

#[derive(Debug, Clone)]
pub struct NXAOBoolCircuit {
    pub input_map: HashMap<WireId, Option<GateId>>,
    pub output_map: HashMap<WireId, GateId>,
    pub gate_map: HashMap<GateId, NXAOBoolGate>,
    pub module_storage: ModuleStorageRef<NXAOBoolGate, Self>,
    //pub module_map: HashMap<ModuleId, Self>,
    pub gate_dependence_map: HashMap<GateId, Vec<GateId>>,
    pub const_gates: Vec<GateId>,
    pub input_len: usize,
    pub output_len: usize,
    //pub num_module: usize,
    pub num_wire: usize,
    pub num_gate: usize,
    pub num_const: usize,
    pub gate_index: usize,
}

impl BoolCircuit<NXAOBoolGate> for NXAOBoolCircuit {
    fn to_ref(self) -> BoolCircuitRef<NXAOBoolGate, Self> {
        BoolCircuitRef::new(self)
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

    fn num_const(&self) -> usize {
        self.num_const
    }

    fn input_to_gate_id(&self, wire_id: &WireId) -> Result<Option<GateId>, BoolCircuitError> {
        self.input_map
            .get(wire_id)
            .ok_or(BoolCircuitError::UnknownInput(*wire_id))
            .and_then(|id| Ok(*id))
    }

    fn output_to_gate_id(&self, wire_id: &WireId) -> Result<GateId, BoolCircuitError> {
        self.output_map
            .get(wire_id)
            .ok_or(BoolCircuitError::UnknownOutput(*wire_id))
            .and_then(|id| Ok(*id))
    }

    fn get_gate(&self, gate_id: &GateId) -> Result<NXAOBoolGate, BoolCircuitError> {
        self.gate_map
            .get(gate_id)
            .ok_or(BoolCircuitError::UnknownGate(*gate_id))
            .and_then(|gate| Ok(gate.clone()))
    }

    fn get_module(
        &self,
        module_id: &ModuleId,
    ) -> Result<BoolCircuitRef<NXAOBoolGate, Self>, BoolCircuitError> {
        self.module_storage.get_module(module_id)
    }

    fn get_depended_gates(&self, gate_id: &GateId) -> Result<Vec<GateId>, BoolCircuitError> {
        let ids = self.gate_dependence_map.get(gate_id);
        match ids {
            None => Ok(Vec::new()),
            Some(ids) => Ok(ids.to_vec()),
        }
    }

    fn get_const_gates(&self) -> Vec<GateId> {
        self.const_gates.to_vec()
    }

    fn input(&mut self) -> Result<GateId, BoolCircuitError> {
        let new_wire_id = WireId(self.input_len as u64);
        let input_gate = InputGate {
            wire_id: new_wire_id,
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

    fn constant(&mut self, value: bool) -> Result<GateId, BoolCircuitError> {
        let const_gate = ConstGate { value };
        let new_gate_id = self.add_gate(NXAOBoolGate::Const(const_gate));
        self.const_gates.push(new_gate_id);
        self.num_const += 1;
        Ok(new_gate_id)
    }

    fn not(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let not_gate = NotGate { id: *gate_id };
        let new_gate_id = self.add_gate(NXAOBoolGate::Not(not_gate));
        self.add_dependence(gate_id, &new_gate_id)?;
        self.num_gate += 1;
        Ok(new_gate_id)
    }

    fn xor(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let xor_gate = XorGate {
            left_id: *gate_l_id,
            right_id: *gate_r_id,
        };
        let new_gate_id = self.add_gate(NXAOBoolGate::Xor(xor_gate));
        self.add_dependence(gate_l_id, &new_gate_id)?;
        self.add_dependence(gate_r_id, &new_gate_id)?;
        self.num_gate += 1;
        Ok(new_gate_id)
    }

    fn and(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let and_gate = AndGate {
            left_id: *gate_l_id,
            right_id: *gate_r_id,
        };
        let new_gate_id = self.add_gate(NXAOBoolGate::And(and_gate));
        self.add_dependence(gate_l_id, &new_gate_id)?;
        self.add_dependence(gate_r_id, &new_gate_id)?;
        self.num_gate += 1;
        Ok(new_gate_id)
    }

    fn or(&mut self, gate_l_id: &GateId, gate_r_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let or_gate = OrGate {
            left_id: *gate_l_id,
            right_id: *gate_r_id,
        };
        let new_gate_id = self.add_gate(NXAOBoolGate::Or(or_gate));
        self.add_dependence(gate_l_id, &new_gate_id)?;
        self.add_dependence(gate_r_id, &new_gate_id)?;
        self.num_gate += 1;
        Ok(new_gate_id)
    }

    fn equivalent(
        &mut self,
        gate_l_id: &GateId,
        gate_r_id: &GateId,
    ) -> Result<GateId, BoolCircuitError> {
        let xor = self.xor(gate_l_id, gate_r_id)?;
        self.not(&xor)
    }

    fn identity(&mut self, gate_id: &GateId) -> Result<GateId, BoolCircuitError> {
        let not1 = self.not(gate_id)?;
        self.not(&not1)
    }

    fn register_module(&mut self, module_circuit: &BoolCircuitRef<NXAOBoolGate, Self>) -> ModuleId {
        self.module_storage.register_module(module_circuit)
    }

    fn sub_circuit(&mut self) -> (ModuleId, BoolCircuitRef<NXAOBoolGate, Self>) {
        let new_circuit = Self::new(self.module_storage.clone());
        let new_ref = new_circuit.to_ref();
        let module_id = self.register_module(&new_ref);
        (module_id, new_ref)
    }

    fn module(
        &mut self,
        module_id: &ModuleId,
        gate_ids: &[GateId],
    ) -> Result<Vec<GateId>, BoolCircuitError> {
        let module_circuit = self.get_module(module_id)?;
        let input_len = module_circuit.input_len();
        let output_len = module_circuit.output_len();
        let num_wire = module_circuit.num_wire();
        let num_gate = module_circuit.num_gate();
        let num_const = module_circuit.num_const();
        self.num_wire += num_wire - input_len - output_len;
        self.num_gate += num_gate;
        self.num_const += num_const;
        let new_gate_ids = (0..output_len)
            .into_iter()
            .map(|i| {
                let module_gate = ModuleGate {
                    input_len,
                    output_len,
                    input_ids: gate_ids.to_vec(),
                    out_index: i,
                    module_id: *module_id,
                };
                self.add_gate(NXAOBoolGate::Module(module_gate))
            })
            .collect::<Vec<GateId>>();
        for input_id in gate_ids.into_iter() {
            for out_id in new_gate_ids.iter() {
                self.add_dependence(input_id, out_id)?;
            }
        }
        Ok(new_gate_ids)
    }

    /*fn modify_with_const_gates(
        &mut self,
        other_const_gate_ids: &[(GateId, bool)],
    ) -> Result<(), BoolCircuitError> {
        let const_gate_ids = self.const_gates.to_vec();
        for gate_id in const_gate_ids.iter() {
            let const_gate = match self.get_gate(&gate_id)? {
                NXAOBoolGate::Const(g) => g,
                _ => {
                    return Err(BoolCircuitError::NotConstGate(*gate_id));
                }
            };
            let value = const_gate.value;
            self.modify_gate_with_fixed_value(gate_id, value)?;
            self.gate_map.remove(gate_id);
            self.gate_dependence_map.remove(gate_id);
        }
        for (gate_id, value) in other_const_gate_ids {
            self.modify_gate_with_fixed_value(gate_id, *value)?;
            self.gate_map.remove(gate_id);
            self.gate_dependence_map.remove(gate_id);
        }
        self.const_gates = Vec::new();
        Ok(())
    }*/
}

impl PartialEq for NXAOBoolCircuit {
    fn eq(&self, other: &Self) -> bool {
        self.input_map == other.input_map
            && self.output_map == other.output_map
            && self.gate_map == other.gate_map
            && self.gate_dependence_map == other.gate_dependence_map
            && self.const_gates == other.const_gates
            && self.input_len == other.input_len
            && self.output_len == other.output_len
            && self.num_wire == other.num_wire
            && self.num_gate == other.num_gate
            && self.gate_index == other.gate_index
    }
}

impl Eq for NXAOBoolCircuit {}

impl NXAOBoolCircuit {
    pub fn new(module_storage: ModuleStorageRef<NXAOBoolGate, Self>) -> Self {
        Self {
            input_map: HashMap::new(),
            output_map: HashMap::new(),
            gate_map: HashMap::new(),
            module_storage,
            gate_dependence_map: HashMap::new(),
            const_gates: Vec::new(),
            input_len: 0,
            output_len: 0,
            num_wire: 0,
            num_gate: 0,
            num_const: 0,
            gate_index: 0,
        }
    }

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

    /*fn modify_gate_with_fixed_value(
        &mut self,
        gate_id: &GateId,
        value: bool,
    ) -> Result<(), BoolCircuitError> {
        let depended_gate_ids = self.get_depended_gates(gate_id)?;
        //println!("gate_id {}, depend_ids {:?}",gate_id, depended_gate_ids);
        for id in depended_gate_ids {
            let gate = self.get_gate(&id)?;
            match gate {
                NXAOBoolGate::Input(_) => {}
                NXAOBoolGate::Const(_) => {}
                NXAOBoolGate::Not(_) => {
                    //println!("fix not gate_id {}, chhild_id {}", *gate_id, id);
                    let fixed_bit_not = !value;
                    self.modify_gate_with_fixed_value(&id, fixed_bit_not)?;
                }
                NXAOBoolGate::Xor(gate) => {
                    //println!("fix xor gate_id {}, chhild_id {}", *gate_id, id);
                    let pair_input_gate_id = if gate.left_id == *gate_id {
                        gate.right_id
                    } else {
                        gate.left_id
                    };
                    if !value {
                        let not = self.not(&pair_input_gate_id)?;
                        let new_gate = NotGate { id: not };
                        self.gate_map.insert(id, NXAOBoolGate::Not(new_gate));
                    } else {
                        let new_not_gate = NotGate {
                            id: pair_input_gate_id,
                        };
                        self.gate_map.insert(id, NXAOBoolGate::Not(new_not_gate));
                    }
                }
                NXAOBoolGate::And(gate) => {
                    //println!("fix and gate_id {}, chhild_id {}", *gate_id, id);
                    let pair_input_gate_id = if gate.left_id == *gate_id {
                        gate.right_id
                    } else {
                        gate.left_id
                    };
                    if !value {
                        self.num_wire -= 1;
                        let dependence = self
                            .gate_dependence_map
                            .get_mut(&pair_input_gate_id)
                            .ok_or(BoolCircuitError::UnknownDependence(pair_input_gate_id))?;
                        for i in 0..dependence.len() {
                            if id == dependence[i] {
                                dependence.remove(i);
                                break;
                            }
                        }
                        self.modify_gate_with_fixed_value(&id, false)?;
                    } else {
                        let not = self.not(&pair_input_gate_id)?;
                        let new_gate = NotGate { id: not };
                        self.gate_map.insert(id, NXAOBoolGate::Not(new_gate));
                    }
                }
                NXAOBoolGate::Or(gate) => {
                    //println!("fix or gate_id {}, chhild_id {}", *gate_id, id);
                    let pair_input_gate_id = if gate.left_id == *gate_id {
                        gate.right_id
                    } else {
                        gate.left_id
                    };
                    if !value {
                        let not = self.not(&pair_input_gate_id)?;
                        let new_gate = NotGate { id: not };
                        self.gate_map.insert(id, NXAOBoolGate::Not(new_gate));
                    } else {
                        self.num_wire -= 1;
                        let dependence = self
                            .gate_dependence_map
                            .get_mut(&pair_input_gate_id)
                            .ok_or(BoolCircuitError::UnknownDependence(pair_input_gate_id))?;
                        for i in 0..dependence.len() {
                            if id == dependence[i] {
                                dependence.remove(i);
                                break;
                            }
                        }
                        self.modify_gate_with_fixed_value(&id, true)?;
                    }
                }
                NXAOBoolGate::Module(gate) => {
                    println!("module id {}",gate.module_id);
                    //println!("fix module gate_id {}, chhild_id {}", *gate_id, id);
                    let first_output_id = GateId(id.0 - (gate.out_index as u64));
                    let output_len = gate.output_len();
                    let input_gates = &gate.input_ids;

                    let index_of_fixed_input_op = input_gates.iter().position(|id| id == gate_id);
                    let index_of_fixed_input = match index_of_fixed_input_op {
                        Some(i) => i,
                        None => return Ok(()),
                    };
                    let module_circuit = self.get_module(&gate.module_id)?;
                    let mut modified_input_wire_id = WireId(0);
                    let mut i = 0;
                    while i <= index_of_fixed_input {
                        if let Some(_) = module_circuit.input_to_gate_id(&modified_input_wire_id)? {
                            if i == index_of_fixed_input {
                                //modified_input_gate_id = id;
                                break;
                            }
                            i += 1;
                        }
                        modified_input_wire_id += WireId(1);
                    }
                    /*module_circuit
                        .gate_map
                        .insert(modified_input_gate_id, NXAOBoolGate::Const(const_gate));
                    module_circuit.input_len -= 1;
                    module_circuit.num_wire -= 1;
                    module_circuit
                        .input_map
                        .insert(modified_input_wire_id, None);
                    let modified_module_id = self.register_module(&module_circuit.to_ref());*/
                    let const_gate = ConstGate { value };
                    let mut fix_vals = (&module_circuit.1).borrow().clone();
                    fix_vals.push((
                        modified_input_wire_id,
                        NXAOBoolGate::Const(const_gate),
                        value,
                    ));
                    let new_c_ref = BoolCircuitRef(
                        module_circuit.0,
                        Rc::new(RefCell::new(fix_vals)),
                        PhantomData,
                    );
                    let new_module_id = self.register_module(&new_c_ref);
                    /*match self.module_fix_input_map.get(&cur_module_id) {
                        Some((parent_id, changes)) => {
                            let mut new_change = changes.clone();
                            new_change.push((modified_input_wire_id, NXAOBoolGate::Const(const_gate)));
                            let parent_id = *parent_id;
                            self.module_fix_input_map.insert(new_module_id, (parent_id, new_change));
                        },
                        None => {
                            self.module_fix_input_map.insert(new_module_id, (cur_module_id, vec![(modified_input_wire_id,  NXAOBoolGate::Const(const_gate))]));
                        }
                    };*/
                    //modified_input_gates.remove(index_of_fixed_input);
                    for i in 0..output_len {
                        let m_id = GateId(first_output_id.0 + (i as u64));
                        let mut m_gate = match self
                            .gate_map
                            .get_mut(&m_id)
                            .ok_or(BoolCircuitError::UnknownGate(m_id))?
                        {
                            NXAOBoolGate::Module(g) => g,
                            _ => return Err(BoolCircuitError::NotModuleGate(m_id)),
                        };
                        /*self.get_gate(&m_id)? {
                            NXAOBoolGate::Module(g) => g.clone(),
                            _ => return Err(BoolCircuitError::NotModuleGate(m_id)),
                        };*/
                        m_gate.input_len -= 1;
                        m_gate.input_ids.remove(index_of_fixed_input);
                        m_gate.module_id = new_module_id;
                        //self.gate_map.insert(m_id, NXAOBoolGate::Module(m_gate));
                    }
                }
            }
        }
        Ok(())
    }*/
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn input1_output1() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id = circuit.input().unwrap();
        circuit.output(input_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 1);
        assert_eq!(circuit.output_len(), 1);
    }

    #[test]
    fn input1_not_ouput1() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id = circuit.input().unwrap();
        let not_gate_id = circuit.not(&input_gate_id).unwrap();
        circuit.output(not_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 1);
        assert_eq!(circuit.output_len(), 1);
    }

    #[test]
    fn input_xor_output1() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let or_gate_id = circuit.xor(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(or_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 2);
        assert_eq!(circuit.output_len(), 1);
    }

    #[test]
    fn input2_and_output1() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let and_gate_id = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(and_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 2);
        assert_eq!(circuit.output_len(), 1);
    }

    #[test]
    fn input2_or_output1() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let or_gate_id = circuit.or(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(or_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 2);
        assert_eq!(circuit.output_len(), 1);
    }

    #[test]
    fn input3_and_or_output1() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let input_gate_id3 = circuit.input().unwrap();
        let and_gate_id = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        let or_gate_id = circuit.or(&and_gate_id, &input_gate_id3).unwrap();
        circuit.output(or_gate_id).unwrap();
        assert_eq!(circuit.input_len(), 3);
        assert_eq!(circuit.output_len(), 1);
    }
}
