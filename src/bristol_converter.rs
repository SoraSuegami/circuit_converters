use crate::bool_circuit::*;
use crate::gates::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::marker::PhantomData;
use std::num::ParseIntError;
use std::path::Path;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum BristolError {
    #[error("The {0}-th line is not found.")]
    NotFoundLine(usize),
    #[error("Fail to split a line.")]
    LineSplitError,
    #[error("Unknown wire {0} exists in the bristol file.")]
    UnknownWire(usize),
    #[error("Unknown gate of id {0} exists in the circuit.")]
    UnknownGate(GateId),
    #[error("The gate {0} is not supported.")]
    NotSupportedGate(String),
    #[error(transparent)]
    CircuitError(#[from] BoolCircuitError),
    #[error(transparent)]
    IOError(#[from] std::io::Error),
    #[error(transparent)]
    ParseIntError(#[from] ParseIntError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BristolReader<G: Gate, C: BoolCircuit<G>> {
    gate_of_wire: HashMap<usize, GateId>,
    _g: PhantomData<G>,
    _c: PhantomData<C>,
}

impl<G: Gate, C: BoolCircuit<G>> BristolReader<G, C> {
    pub fn new() -> Self {
        Self {
            gate_of_wire: HashMap::new(),
            _g: PhantomData,
            _c: PhantomData,
        }
    }

    pub fn read_file(&mut self, filepath: &Path) -> Result<C, BristolError> {
        let mut circuit = C::new();
        let reader = BufReader::new(File::open(filepath)?);
        let mut lines_iter = reader.lines();
        let first_strs = lines_iter.next().ok_or(BristolError::NotFoundLine(1))??;
        let mut _first_strs = first_strs.split_whitespace();
        /*let num_gate = first_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        let num_wire = first_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;*/
        let second_strs = lines_iter.next().ok_or(BristolError::NotFoundLine(1))??;
        let mut second_strs = second_strs.split_whitespace();
        let num_input = second_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        //let input_bits = Vec::new();
        let mut input_len_sum = 0;
        for _ in 0..num_input {
            let input_bit = second_strs
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            //input_bits.push(input_bit);
            for j in 0..input_bit {
                self.gate_of_wire
                    .insert(input_len_sum + j, circuit.input()?);
            }
            input_len_sum += input_bit;
        }
        let third_strs = lines_iter.next().ok_or(BristolError::NotFoundLine(1))??;
        let mut third_strs = third_strs.split_whitespace();
        let num_output = third_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        //let output_bits = Vec::new();
        //let mut output_len_sum = 0;
        for _ in 0..num_output {
            let _output_bit = third_strs
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            //output_len_sum += output_bit;
        }
        //skip one row.
        let _ = lines_iter.next().ok_or(BristolError::NotFoundLine(1))?;

        for result in lines_iter {
            let l = result?;
            let mut l = l.split_whitespace();
            let input_len = l
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            let output_len = l
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            let mut input_gates = Vec::new();
            for _ in 0..input_len {
                let wire_id = l
                    .next()
                    .ok_or(BristolError::LineSplitError)?
                    .parse::<usize>()?;
                let gate_id = self
                    .gate_of_wire
                    .get(&wire_id)
                    .ok_or(BristolError::UnknownWire(wire_id))?;
                input_gates.push(gate_id);
            }
            let mut output_wire_ids = Vec::new();
            for _ in 0..output_len {
                let output_wire_id = l
                    .next()
                    .ok_or(BristolError::LineSplitError)?
                    .parse::<usize>()?;
                output_wire_ids.push(output_wire_id);
            }
            let gate_type = l.next().ok_or(BristolError::LineSplitError)?;

            match gate_type {
                "INV" => {
                    let output_gate = circuit.not(input_gates[0])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                "XOR" => {
                    let output_gate = circuit.xor(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                "AND" => {
                    let output_gate = circuit.and(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                "OR" => {
                    let output_gate = circuit.or(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                _ => {
                    return Err(BristolError::NotSupportedGate(gate_type.to_string()));
                }
            };
        }

        Ok(circuit)
    }
}

pub struct BristolNXAOWriter {
    circuit: NXAOBoolCircuit,
    num_wire: usize,
}

impl BristolNXAOWriter {
    pub fn new(circuit: NXAOBoolCircuit) -> Self {
        Self {
            circuit,
            num_wire: 0,
        }
    }

    pub fn write_file(&mut self, filepath: &Path, circuit: &NXAOBoolCircuit) -> Result<(), BristolError> {
        let output_len = circuit.output_len();
        let mut wire_of_gate = HashMap::new();
        for i in 0..output_len {
            let output_wire_id = WireId(i as u64);
            let output_gate_id = self.circuit.output_to_gate_id(&output_wire_id)?.clone();
            let output_gate = self.circuit.get_gate(&output_gate_id)?.clone();
            self.write_single_gate(filepath, &output_gate_id, output_gate, &mut wire_of_gate)?;
        }
        Ok(())
    }

    fn write_single_gate(
        &mut self,
        filepath: &Path,
        gate_id: &GateId,
        gate: NXAOBoolGate,
        wire_of_gate: &mut HashMap<GateId, usize>,
    ) -> Result<(), BristolError> {
        match gate {
            NXAOBoolGate::Input(_) => {
                self.update_wire(gate_id, wire_of_gate)
            }
            NXAOBoolGate::Not(gate) => {
                if wire_of_gate.get(&gate.id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.id)?.clone();
                    self.write_single_gate(filepath, &gate.id, input_gate,wire_of_gate)?;
                }
                self.update_wire(gate_id, wire_of_gate)
            }
            NXAOBoolGate::Xor(gate) => {
                if wire_of_gate.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(filepath, &gate.left_id, input_gate,wire_of_gate)?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(filepath, &gate.right_id, input_gate,wire_of_gate)?;
                }
                self.update_wire(gate_id, wire_of_gate)
            }
            NXAOBoolGate::And(gate) => {
                if wire_of_gate.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(filepath, &gate.left_id, input_gate,wire_of_gate)?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(filepath, &gate.right_id, input_gate,wire_of_gate)?;
                }
                self.update_wire(gate_id, wire_of_gate)
            }
            NXAOBoolGate::Or(gate) => {
                if wire_of_gate.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(filepath, &gate.left_id, input_gate,wire_of_gate)?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(filepath, &gate.right_id, input_gate,wire_of_gate)?;
                }
                self.update_wire(gate_id, wire_of_gate)
            }
            _ => Err(BristolError::NotSupportedGate(gate.to_str())),
        }
    }

    fn update_wire(
        &mut self,
        gate_id: &GateId,
        wire_of_gate: &mut HashMap<GateId, usize>,
    ) -> Result<(),BristolError> {
        wire_of_gate.insert(*gate_id, self.num_wire);
        self.num_wire += 1;
        Ok(())
    }
}

