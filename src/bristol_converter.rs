use crate::bool_circuit::*;
use crate::gates::*;
use std::collections::HashMap;
use std::fs::File;
use std::hash::Hash;
use std::io::{self, BufRead, BufReader};
use std::marker::PhantomData;
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
    #[error("The gate {0} is not supported.")]
    NotSupportedGate(String),
    #[error(transparent)]
    CircuitError(#[from] BoolCircuitError),
    #[error(transparent)]
    iOError(#[from] std::io::Error),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BristolConverter<G: Gate, C: BoolCircuit<G>> {
    gate_of_wire: HashMap<usize, GateId>,
    _g: PhantomData<G>,
    _c: PhantomData<C>,
}

impl<G: Gate, C: BoolCircuit<G>> BristolConverter<G, C> {
    pub fn new() -> Self {
        Self {
            gate_of_wire: HashMap::new(),
            _g: PhantomData,
            _c: PhantomData,
        }
    }

    pub fn read_file(&mut self,filepath: &Path) -> Result<C, BristolError> {
        let circuit = C::new();
        let reader = BufReader::new(File::open(filepath)?);
        let lines_iter = reader.lines();
        let first_strs = lines_iter
            .next()
            .ok_or(BristolError::NotFoundLine(1))??
            .split_whitespace();
        let num_gate = first_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        let num_wire = first_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        let second_strs = lines_iter
            .next()
            .ok_or(BristolError::NotFoundLine(1))??
            .split_whitespace();
        let num_input = second_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        //let input_bits = Vec::new();
        let input_len_sum = 0;
        for i in 0..num_input {
            let input_bit = second_strs
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            //input_bits.push(input_bit);
            for j in 0..input_bit {
                self.gate_of_wire.insert(input_len_sum+j, circuit.input());
            }
            input_len_sum += input_bit;
        }
        let third_strs = lines_iter
            .next()
            .ok_or(BristolError::NotFoundLine(1))??
            .split_whitespace();
        let num_output = third_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        //let output_bits = Vec::new();
        let output_len_sum = 0;
        for i in 0..num_output {
            let output_bit = third_strs
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            output_len_sum += output_bit;
        }
        //skip one row.
        lines_iter.next().ok_or(BristolError::NotFoundLine(1))?;

        for result in lines_iter {
            let l = result?.split_whitespace();
            let input_len = l
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            let output_len = l
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            let input_gates = Vec::new();
            for j in 0..input_len {
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
            for j in 0..output_len {
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
