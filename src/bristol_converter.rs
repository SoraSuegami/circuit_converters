use crate::bool_circuit::*;
use crate::gates::*;
use std::collections::HashMap;
//use std::fs::File;
use std::fmt::Write;
use std::io::BufRead;
use std::marker::PhantomData;
use std::num::ParseIntError;
//use std::path::Path;
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
    #[error("The {0}-th output gate should be either NOT, XOR, AND, OR gate.")]
    InvalidOutputGate(WireId),
    #[error("The gate {0} is not supported.")]
    NotSupportedGate(String),
    #[error(transparent)]
    CircuitError(#[from] BoolCircuitError),
    #[error(transparent)]
    IOError(#[from] std::io::Error),
    #[error(transparent)]
    FmtError(#[from] std::fmt::Error),
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

    pub fn read<R: BufRead>(&mut self, reader: R) -> Result<C, BristolError> {
        let mut circuit = C::new();
        //let reader = BufReader::new(File::open(filepath)?);
        let mut lines_iter = reader.lines();
        let first_strs = lines_iter.next().ok_or(BristolError::NotFoundLine(1))??;
        let mut first_strs = first_strs.split_whitespace();
        let _ = first_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        let num_wire = first_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
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
        let mut output_len_sum = 0;
        for _ in 0..num_output {
            let output_bit = third_strs
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            output_len_sum += output_bit;
        }
        //skip one row.
        let _ = lines_iter.next().ok_or(BristolError::NotFoundLine(1))?;

        //let mut num_remain_gate = num_gate;

        for result in lines_iter {
            let l = result?;
            if l.len() == 0 {
                break;
            }
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
                    //Ok(output_gate)
                }
                "XOR" => {
                    let output_gate = circuit.xor(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                    //Ok(output_gate)
                }
                "AND" => {
                    let output_gate = circuit.and(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                    //Ok(output_gate)
                }
                "OR" => {
                    let output_gate = circuit.or(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                    //Ok(output_gate)
                }
                "EQ" | "EQW" => {
                    let output_gate = circuit.identity(input_gates[0])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                _ => return Err(BristolError::NotSupportedGate(gate_type.to_string())),
            };
            /*if num_remain_gate <= output_len_sum {
                circuit.output(output_gate)?;
            }

            num_remain_gate -= 1;*/
        }

        for i in (num_wire - output_len_sum)..num_wire {
            let gate_id = self.gate_of_wire[&i];
            circuit.output(gate_id)?;
        }

        Ok(circuit)
    }
}

pub type BristolNXAOReader = BristolReader<NXAOBoolGate, NXAOBoolCircuit>;

#[derive(Debug)]
pub struct BristolNXAOWriter<W: Write> {
    pub circuit: NXAOBoolCircuit,
    pub num_wire: usize,
    pub writer: W,
}

impl<W: Write> BristolNXAOWriter<W> {
    pub fn new(circuit: NXAOBoolCircuit, writer: W) -> Self {
        Self {
            circuit,
            num_wire: 0,
            writer,
        }
    }

    pub fn write(
        &mut self,
        wire_of_gate: Option<&mut HashMap<GateId, usize>>,
    ) -> Result<(), BristolError> {
        let input_len = self.circuit.input_len();
        let output_len = self.circuit.output_len();
        let num_gate = self.circuit.num_gate();
        let num_wire = self.circuit.num_wire();
        let first_line = format!("{} {}\n", num_gate, num_wire);
        self.writer.write_str(&first_line)?;

        let second_line = format!("1 {}\n", input_len);
        self.writer.write_str(&second_line)?;
        let third_line = format!("1 {}\n", output_len);
        self.writer.write_str(&third_line)?;
        self.writer.write_str("\n")?;

        let mut new_wire_of_gate = HashMap::<GateId, usize>::new();
        let wire_of_gate = match wire_of_gate {
            Some(m) => m,
            None => &mut new_wire_of_gate,
        };
        self.write_all_gates(wire_of_gate)
    }

    fn write_all_gates(
        &mut self,
        wire_of_gate: &mut HashMap<GateId, usize>,
    ) -> Result<(), BristolError> {
        let output_len = self.circuit.output_len();
        let mut output_gate_ids = Vec::new();
        let mut output_gates = Vec::new();
        for i in 0..output_len {
            let output_wire_id = WireId(i as u64);
            let output_gate_id = self.circuit.output_to_gate_id(&output_wire_id)?.clone();
            let output_gate = self.circuit.get_gate(&output_gate_id)?.clone();
            output_gate_ids.push(output_gate_id);
            output_gates.push(output_gate.clone());
            match output_gate {
                NXAOBoolGate::Input(_) => {}
                NXAOBoolGate::Not(gate) => {
                    let input_gate = self.circuit.get_gate(&gate.id)?.clone();
                    self.write_single_gate(&gate.id, &input_gate, wire_of_gate)?;
                }
                NXAOBoolGate::Xor(gate) => {
                    let l_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(&gate.left_id, &l_gate, wire_of_gate)?;
                    let r_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(&gate.right_id, &r_gate, wire_of_gate)?;
                }
                NXAOBoolGate::And(gate) => {
                    let l_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(&gate.left_id, &l_gate, wire_of_gate)?;
                    let r_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(&gate.right_id, &r_gate, wire_of_gate)?;
                }
                NXAOBoolGate::Or(gate) => {
                    let l_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(&gate.left_id, &l_gate, wire_of_gate)?;
                    let r_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(&gate.right_id, &r_gate, wire_of_gate)?;
                }
                NXAOBoolGate::Module(gate) => {
                    for id in gate.input_gate_ids() {
                        let input_gate = self.circuit.get_gate(&id)?.clone();
                        self.write_single_gate(&id, &input_gate, wire_of_gate)?;
                    }
                }
            }
        }

        for i in 0..output_len {
            let gate_id = output_gate_ids[i];
            let gate = &output_gates[i];
            self.write_single_gate(&gate_id, gate, wire_of_gate)?;
        }
        Ok(())
    }

    fn write_single_gate(
        &mut self,
        gate_id: &GateId,
        gate: &NXAOBoolGate,
        wire_of_gate: &mut HashMap<GateId, usize>,
    ) -> Result<(), BristolError> {
        match gate {
            NXAOBoolGate::Input(gate) => {
                self.update_wire(gate_id, 0, None, &gate.to_str(), wire_of_gate)
            }
            NXAOBoolGate::Not(gate) => {
                if wire_of_gate.get(&gate.id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.id)?.clone();
                    self.write_single_gate(&gate.id, &input_gate, wire_of_gate)?;
                }
                let input_wire = wire_of_gate[&gate.id];
                self.update_wire(
                    gate_id,
                    1,
                    Some(&[input_wire]),
                    &gate.to_str(),
                    wire_of_gate,
                )
            }
            NXAOBoolGate::Xor(gate) => {
                if wire_of_gate.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(&gate.left_id, &input_gate, wire_of_gate)?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(&gate.right_id, &input_gate, wire_of_gate)?;
                }
                let l_wire = wire_of_gate[&gate.left_id];
                let r_wire = wire_of_gate[&gate.right_id];
                self.update_wire(
                    gate_id,
                    2,
                    Some(&[l_wire, r_wire]),
                    &gate.to_str(),
                    wire_of_gate,
                )
            }
            NXAOBoolGate::And(gate) => {
                if wire_of_gate.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(&gate.left_id, &input_gate, wire_of_gate)?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(&gate.right_id, &input_gate, wire_of_gate)?;
                }
                let l_wire = wire_of_gate[&gate.left_id];
                let r_wire = wire_of_gate[&gate.right_id];
                self.update_wire(
                    gate_id,
                    2,
                    Some(&[l_wire, r_wire]),
                    &gate.to_str(),
                    wire_of_gate,
                )
            }
            NXAOBoolGate::Or(gate) => {
                if wire_of_gate.get(&gate.left_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(&gate.left_id, &input_gate, wire_of_gate)?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    let input_gate = self.circuit.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(&gate.right_id, &input_gate, wire_of_gate)?;
                }
                let l_wire = wire_of_gate[&gate.left_id];
                let r_wire = wire_of_gate[&gate.right_id];
                self.update_wire(
                    gate_id,
                    2,
                    Some(&[l_wire, r_wire]),
                    &gate.to_str(),
                    wire_of_gate,
                )
            }
            NXAOBoolGate::Module(gate) => {
                let input_ids = gate.input_gate_ids();
                for id in &input_ids {
                    if wire_of_gate.get(id).is_none() {
                        let input_gate = self.circuit.get_gate(id)?.clone();
                        self.write_single_gate(&id, &input_gate, wire_of_gate)?;
                    }
                }
                let module_circuit = self.circuit.get_module(&gate.module_id)?.clone();
                let sub_str = String::new();
                let mut sub_writer = BristolNXAOWriter::<String>::new(module_circuit, sub_str);
                sub_writer.num_wire = self.num_wire;
                sub_writer.write_all_gates(wire_of_gate)?;
                self.writer.write_str(&sub_writer.writer)?;
                Ok(())
                //self.update_wire(gate_id, , Some(&[l_wire, r_wire]), &gate.to_str(), wire_of_gate)
            }
            //_ => Err(BristolError::NotSupportedGate(gate.to_str())),
        }
    }

    fn update_wire(
        &mut self,
        gate_id: &GateId,
        num_input: usize,
        input_wires: Option<&[usize]>,
        gate_str: &str,
        wire_of_gate: &mut HashMap<GateId, usize>,
    ) -> Result<(), BristolError> {
        wire_of_gate.insert(*gate_id, self.num_wire);
        match input_wires {
            Some(wires) => {
                let mut write_str = format!("{} 1 ", num_input);
                for i in 0..num_input {
                    write_str = write_str + &format!("{} ", wires[i]);
                }
                write_str = write_str + &format!("{} ", self.num_wire) + gate_str + "\n";
                self.writer.write_str(&write_str)?;
            }
            None => {}
        };
        self.num_wire += 1;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::BufReader;
    #[test]
    fn not_test() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id = circuit.input().unwrap();
        let not = circuit.not(&input_gate_id).unwrap();
        circuit.output(not).unwrap();

        let write_str = String::new();
        let mut writer = BristolNXAOWriter::new(circuit.clone(), write_str);
        writer.write(None).unwrap();
        println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let buf_read = BufReader::new(writer.writer.as_bytes());
        let read_circuit = reader.read(buf_read).unwrap();
        assert_eq!(circuit, read_circuit);
    }

    #[test]
    fn xor_test() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let not = circuit.xor(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(not).unwrap();

        let write_str = String::new();
        let mut writer = BristolNXAOWriter::new(circuit.clone(), write_str);
        writer.write(None).unwrap();
        println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let buf_read = BufReader::new(writer.writer.as_bytes());
        let read_circuit = reader.read(buf_read).unwrap();
        assert_eq!(circuit, read_circuit);
    }

    #[test]
    fn and_test() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let not = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(not).unwrap();

        let write_str = String::new();
        let mut writer = BristolNXAOWriter::new(circuit.clone(), write_str);
        writer.write(None).unwrap();
        println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let buf_read = BufReader::new(writer.writer.as_bytes());
        let read_circuit = reader.read(buf_read).unwrap();
        assert_eq!(circuit, read_circuit);
    }

    #[test]
    fn or_test() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let not = circuit.or(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(not).unwrap();

        let write_str = String::new();
        let mut writer = BristolNXAOWriter::new(circuit.clone(), write_str);
        writer.write(None).unwrap();
        println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let buf_read = BufReader::new(writer.writer.as_bytes());
        let read_circuit = reader.read(buf_read).unwrap();
        assert_eq!(circuit, read_circuit);
    }

    #[test]
    fn module_1_test() {
        let mut circuit = NXAOBoolCircuit::new();
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let mut eq_circuit = NXAOBoolCircuit::new();
        let eq_input_gate_id1 = eq_circuit.input().unwrap();
        let eq_input_gate_id2 = eq_circuit.input().unwrap();
        let eq_xor = eq_circuit
            .xor(&eq_input_gate_id1, &eq_input_gate_id2)
            .unwrap();
        let eq_not = eq_circuit.not(&eq_xor).unwrap();
        eq_circuit.output(eq_not).unwrap();
        let eq_module_id = circuit.register_module(eq_circuit);
        let call_inputs = [input_gate_id1, input_gate_id2];
        let eq_call = circuit.module(&eq_module_id, &call_inputs).unwrap();
        circuit.output(eq_call[0]).unwrap();

        let write_str = String::new();
        let mut writer = BristolNXAOWriter::new(circuit.clone(), write_str);
        writer.write(None).unwrap();
        println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let buf_read = BufReader::new(writer.writer.as_bytes());
        let read_circuit = reader.read(buf_read);
        assert!(read_circuit.is_ok());
        //assert_eq!(circuit,read_circuit);
    }
}
