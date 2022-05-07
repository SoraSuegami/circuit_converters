use crate::bool_circuit::*;
use crate::gates::*;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum EvaluatorError {
    #[error("The evaled bit of the gate id {0} is unknown.")]
    UnknownEvaledBit(GateId),
    #[error("The number of given inputs is {0}, but the input length is {1}.")]
    InvalidInputLen(usize, usize),
    #[error("The gate of the gate id {0} is not supported.")]
    NotSupportedGate(GateId),
    #[error(transparent)]
    CircuitError(#[from] BoolCircuitError),
}

pub trait BoolEvaluator<G: Gate, C: BoolCircuit<G>> {
    fn circuit(&self) -> &C;
    fn eval_output(&mut self, inputs: &[bool]) -> Result<Vec<bool>, EvaluatorError> {
        let circuit = self.circuit();
        let output_len = circuit.output_len();
        let mut outputs = Vec::new();
        for i in 0..output_len {
            let wire_id = WireId(i as u64);
            let output = self.eval_single_output(inputs, &wire_id, None)?;
            outputs.push(output);
        }
        Ok(outputs)
    }

    fn eval_single_output(
        &mut self,
        inputs: &[bool],
        wire_id: &WireId,
        evaled_map: Option<&mut HashMap<GateId, bool>>,
    ) -> Result<bool, EvaluatorError>;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NXAOBoolEvaluator {
    pub circuit: NXAOBoolCircuit,
}

impl BoolEvaluator<NXAOBoolGate, NXAOBoolCircuit> for NXAOBoolEvaluator {
    fn circuit(&self) -> &NXAOBoolCircuit {
        &self.circuit
    }

    fn eval_single_output(
        &mut self,
        inputs: &[bool],
        wire_id: &WireId,
        evaled_map: Option<&mut HashMap<GateId, bool>>,
    ) -> Result<bool, EvaluatorError> {
        if inputs.len() != self.circuit.input_len() {
            return Err(EvaluatorError::InvalidInputLen(
                inputs.len(),
                self.circuit.input_len(),
            ));
        }
        if wire_id.0 >= (self.circuit.output_len() as u64) {
            return Err(EvaluatorError::CircuitError(
                BoolCircuitError::UnknownOutput(*wire_id),
            ));
        }

        let mut new_evaled_map = HashMap::<GateId, bool>::new();
        let evaled_map = match evaled_map {
            Some(m) => m,
            None => &mut new_evaled_map,
        };

        let output_gate_id = self.circuit.output_to_gate_id(wire_id)?;
        let output_gate = self.circuit.get_gate(&output_gate_id)?;
        self.eval_single_gate(inputs, output_gate_id, output_gate, evaled_map)?;
        let output_bit = evaled_map
            .get(output_gate_id)
            .ok_or(EvaluatorError::UnknownEvaledBit(*output_gate_id))?;
        Ok(*output_bit)
    }
}

impl NXAOBoolEvaluator {
    pub fn new(circuit: NXAOBoolCircuit) -> Self {
        Self { circuit }
    }

    fn eval_single_gate(
        &self,
        inputs: &[bool],
        gate_id: &GateId,
        gate: &NXAOBoolGate,
        evaled_map: &mut HashMap<GateId, bool>,
    ) -> Result<(), EvaluatorError> {
        match gate {
            NXAOBoolGate::Input(gate) => {
                let input_bit: bool = inputs[gate.wire_id.0 as usize];
                evaled_map.insert(*gate_id, input_bit);
                Ok(())
            }
            NXAOBoolGate::Not(gate) => {
                if evaled_map.get(&gate.id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.id)?;
                    self.eval_single_gate(inputs, &gate.id, &input_gate, evaled_map)?;
                }
                let input_bit = evaled_map
                    .get(&gate.id)
                    .ok_or(EvaluatorError::UnknownEvaledBit(gate.id))?;
                let output_bit = !input_bit;
                evaled_map.insert(*gate_id, output_bit);
                Ok(())
            }
            NXAOBoolGate::Xor(gate) => {
                if evaled_map.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?;
                    self.eval_single_gate(inputs, &gate.left_id, &input_gate, evaled_map)?;
                }
                if evaled_map.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?;
                    self.eval_single_gate(inputs, &gate.right_id, &input_gate, evaled_map)?;
                }
                let input_bit_l = evaled_map
                    .get(&gate.left_id)
                    .ok_or(EvaluatorError::UnknownEvaledBit(gate.left_id))?;
                let input_bit_r = evaled_map
                    .get(&gate.right_id)
                    .ok_or(EvaluatorError::UnknownEvaledBit(gate.right_id))?;
                let output_bit = *input_bit_l ^ *input_bit_r;
                evaled_map.insert(*gate_id, output_bit);
                Ok(())
            }
            NXAOBoolGate::And(gate) => {
                if evaled_map.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?;
                    self.eval_single_gate(inputs, &gate.left_id, &input_gate, evaled_map)?;
                }
                if evaled_map.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?;
                    self.eval_single_gate(inputs, &gate.right_id, &input_gate, evaled_map)?;
                }
                let input_bit_l = evaled_map
                    .get(&gate.left_id)
                    .ok_or(EvaluatorError::UnknownEvaledBit(gate.left_id))?;
                let input_bit_r = evaled_map
                    .get(&gate.right_id)
                    .ok_or(EvaluatorError::UnknownEvaledBit(gate.right_id))?;
                let output_bit = *input_bit_l & *input_bit_r;
                evaled_map.insert(*gate_id, output_bit);
                Ok(())
            }
            NXAOBoolGate::Or(gate) => {
                if evaled_map.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?;
                    self.eval_single_gate(inputs, &gate.left_id, &input_gate, evaled_map)?;
                }
                if evaled_map.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?;
                    self.eval_single_gate(inputs, &gate.right_id, &input_gate, evaled_map)?;
                }
                let input_bit_l = evaled_map
                    .get(&gate.left_id)
                    .ok_or(EvaluatorError::UnknownEvaledBit(gate.left_id))?;
                let input_bit_r = evaled_map
                    .get(&gate.right_id)
                    .ok_or(EvaluatorError::UnknownEvaledBit(gate.right_id))?;
                let output_bit = *input_bit_l | *input_bit_r;
                evaled_map.insert(*gate_id, output_bit);
                Ok(())
            }
            NXAOBoolGate::Module(gate) => {
                let input_ids = gate.input_gate_ids();
                for id in &input_ids {
                    if evaled_map.get(id).is_none() {
                        let input_gate = self.circuit.get_gate(id)?;
                        self.eval_single_gate(inputs, id, &input_gate, evaled_map)?;
                    }
                }
                let input_bits = input_ids
                    .iter()
                    .map(|id| {
                        evaled_map
                            .get(id)
                            .ok_or(EvaluatorError::UnknownEvaledBit(*id))
                            .and_then(|b| Ok(*b))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let module_circuit = self.circuit.get_module(&gate.module_id)?;
                let mut evaluator = Self::new(module_circuit.clone());
                let output_bits = evaluator.eval_output(&input_bits)?;
                let first_output_id = GateId(gate_id.0 - (gate.out_index as u64));
                for i in 0..gate.output_len() {
                    let output_id = GateId(first_output_id.0 + (i as u64));
                    evaled_map.insert(output_id, output_bits[i]);
                }
                Ok(())
            }
        }
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
        let mut evaluator = NXAOBoolEvaluator::new(circuit);

        let inputs = vec![true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);
    }

    #[test]
    fn input1_not_ouput1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id = circuit.input().unwrap();
        let not_gate_id = circuit.not(&input_gate_id).unwrap();
        circuit.output(not_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);

        let inputs = vec![true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);
    }

    #[test]
    fn input_xor_output1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let or_gate_id = circuit.xor(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(or_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);

        let inputs = vec![true, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![true, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![false, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![false, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);
    }

    #[test]
    fn input2_and_output1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let and_gate_id = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(and_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);

        let inputs = vec![true, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![true, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![false, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![false, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);
    }

    #[test]
    fn input2_or_output1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let or_gate_id = circuit.or(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(or_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);

        let inputs = vec![true, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![true, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![false, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![false, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);
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
        let mut evaluator = NXAOBoolEvaluator::new(circuit);

        let inputs = vec![true, true, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![true, true, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![true, false, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![true, false, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![false, true, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![false, true, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![false, false, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![false, false, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);
    }

    #[test]
    fn module_1() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let mut eq_circuit = NXAOBoolCircuit::new();
        let eq_input_gate_id1 = eq_circuit.input().unwrap();
        let eq_input_gate_id2 = eq_circuit.input().unwrap();
        let eq_xor = eq_circuit.xor(&eq_input_gate_id1, &eq_input_gate_id2).unwrap();
        let eq_not = eq_circuit.not(&eq_xor).unwrap();
        eq_circuit.output(eq_not).unwrap();
        let eq_module_id = circuit.register_module(eq_circuit);
        let call_inputs = [input_gate_id1,input_gate_id2];
        let eq_call = circuit.module(&eq_module_id, &call_inputs).unwrap();
        circuit.output(eq_call[0]).unwrap();
        
        let mut evaluator = NXAOBoolEvaluator::new(circuit);

        let inputs = vec![true, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![true, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![false, true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![false, false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);
    }
}
