use crate::bool_circuit::*;
use crate::gates::*;
use std::collections::HashMap;
//use std::fs::File;
use std::io::{BufRead, BufWriter, Write};
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
    #[error("The constant gate of id {0} cannot be written to a bristol file.")]
    ConstGateInWriter(GateId),
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

    pub fn read<R: BufRead>(
        &mut self,
        reader: R,
        c_ref: &mut BoolCircuitRef<G, C>,
    ) -> Result<(), BristolError> {
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
        let second_strs = lines_iter.next().ok_or(BristolError::NotFoundLine(2))??;
        let mut second_strs = second_strs.split_whitespace();
        let num_input = second_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        let mut input_len_sum = 0;
        for _ in 0..num_input {
            let input_bit = second_strs
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            for j in 0..input_bit {
                self.gate_of_wire.insert(input_len_sum + j, c_ref.input()?);
            }
            input_len_sum += input_bit;
        }
        let third_strs = lines_iter.next().ok_or(BristolError::NotFoundLine(3))??;
        let mut third_strs = third_strs.split_whitespace();
        let num_output = third_strs
            .next()
            .ok_or(BristolError::LineSplitError)?
            .parse::<usize>()?;
        let mut output_len_sum = 0;
        for _ in 0..num_output {
            let output_bit = third_strs
                .next()
                .ok_or(BristolError::LineSplitError)?
                .parse::<usize>()?;
            output_len_sum += output_bit;
        }
        //skip one row.
        let _ = lines_iter.next().ok_or(BristolError::NotFoundLine(4))?;

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
                    let output_gate = c_ref.not(input_gates[0])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                "XOR" => {
                    let output_gate = c_ref.xor(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                "AND" => {
                    let output_gate = c_ref.and(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                "OR" => {
                    let output_gate = c_ref.or(input_gates[0], input_gates[1])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                "EQ" | "EQW" => {
                    let output_gate = c_ref.identity(input_gates[0])?;
                    self.gate_of_wire.insert(output_wire_ids[0], output_gate);
                }
                _ => return Err(BristolError::NotSupportedGate(gate_type.to_string())),
            };
        }

        for i in (num_wire - output_len_sum)..num_wire {
            let gate_id = self.gate_of_wire[&i];
            c_ref.output(gate_id)?;
        }
        Ok(())
    }
}

pub type BristolNXAOReader = BristolReader<NXAOBoolGate, NXAOBoolCircuit>;

#[derive(Debug)]
pub struct BristolNXAOWriter<W: Write> {
    pub c_ref: BoolCircuitRef<NXAOBoolGate, NXAOBoolCircuit>,
    pub num_wire: usize,
    pub last_const_wire: usize,
    pub writer: BufWriter<W>,
}

impl<W: Write> BristolNXAOWriter<W> {
    pub fn new(c_ref: BoolCircuitRef<NXAOBoolGate, NXAOBoolCircuit>, writer: BufWriter<W>) -> Self {
        Self {
            c_ref,
            num_wire: 0,
            last_const_wire: 0,
            writer,
        }
    }

    pub fn write(
        &mut self,
        num_first_input: usize,
        wire_of_gate: Option<&mut HashMap<GateId, usize>>,
    ) -> Result<HashMap<usize, bool>, BristolError> {
        let input_len = self.c_ref.input_len();
        let output_len = self.c_ref.output_len();
        let num_const = self.c_ref.num_const();
        let num_gate = self.c_ref.num_gate();
        let num_wire = self.c_ref.num_wire();
        let first_line = format!("{} {}\n", num_gate, num_wire + num_const);
        self.writer.write_all(first_line.as_bytes())?;

        let num_all_input = input_len + num_const;
        assert!(num_all_input >= num_first_input);
        let second_line = format!(
            "2 {} {}\n",
            num_first_input,
            num_all_input - num_first_input
        );
        self.writer.write_all(second_line.as_bytes())?;
        let third_line = format!("1 {}\n", output_len);
        self.writer.write_all(third_line.as_bytes())?;
        self.writer.write_all(b"\n")?;

        let mut new_wire_of_gate = HashMap::<GateId, usize>::new();
        let wire_of_gate = match wire_of_gate {
            Some(m) => m,
            None => &mut new_wire_of_gate,
        };
        let mut const_of_wire = HashMap::new();
        let mut last_input_wire_id = WireId(0);
        let mut i = 0;
        while i < input_len {
            let gate_id = self.c_ref.input_to_gate_id(&last_input_wire_id)?.clone();
            match gate_id {
                Some(id) => {
                    let gate = self.c_ref.get_gate(&id)?.clone();
                    self.write_single_gate(&id, &gate, wire_of_gate, &mut const_of_wire)?;
                    i += 1;
                }
                None => {}
            };
            last_input_wire_id += WireId(1);
        }
        self.last_const_wire = input_len;
        self.num_wire += num_const;
        self.write_all_gates(wire_of_gate, &mut const_of_wire)?;
        Ok(const_of_wire)
    }

    fn write_all_gates(
        &mut self,
        wire_of_gate: &mut HashMap<GateId, usize>,
        const_of_wire: &mut HashMap<usize, bool>,
    ) -> Result<(), BristolError> {
        //println!("write all");
        for gate_id in self.c_ref.get_const_gates().iter() {
            let gate = self.c_ref.get_gate(gate_id)?;
            if let NXAOBoolGate::Const(g) = gate {
                let value = g.value;
                wire_of_gate.insert(*gate_id, self.last_const_wire);
                const_of_wire.insert(self.last_const_wire, value);
                self.last_const_wire += 1;
            }
        }

        let output_len = self.c_ref.output_len();
        //self.c_ref.modify_with_const_gates()?;
        let mut output_gate_ids = Vec::new();
        let mut output_gates = Vec::new();
        for i in 0..output_len {
            let output_wire_id = WireId(i as u64);
            let output_gate_id = self.c_ref.output_to_gate_id(&output_wire_id)?.clone();
            let output_gate = self.c_ref.get_gate(&output_gate_id)?.clone();
            output_gate_ids.push(output_gate_id);
            output_gates.push(output_gate.clone());
            match output_gate {
                NXAOBoolGate::Input(_) => {}
                NXAOBoolGate::Const(_) => {}
                NXAOBoolGate::Not(gate) => {
                    if wire_of_gate.get(&gate.id).is_none() {
                        let input_gate = self.c_ref.get_gate(&gate.id)?.clone();
                        self.write_single_gate(&gate.id, &input_gate, wire_of_gate, const_of_wire)?;
                    }
                }
                NXAOBoolGate::Xor(gate) => {
                    if wire_of_gate.get(&gate.left_id).is_none() {
                        let input_gate = self.c_ref.get_gate(&gate.left_id)?.clone();
                        self.write_single_gate(
                            &gate.left_id,
                            &input_gate,
                            wire_of_gate,
                            const_of_wire,
                        )?;
                    }
                    if wire_of_gate.get(&gate.right_id).is_none() {
                        let input_gate = self.c_ref.get_gate(&gate.right_id)?.clone();
                        self.write_single_gate(
                            &gate.right_id,
                            &input_gate,
                            wire_of_gate,
                            const_of_wire,
                        )?;
                    }
                }
                NXAOBoolGate::And(gate) => {
                    if wire_of_gate.get(&gate.left_id).is_none() {
                        let input_gate = self.c_ref.get_gate(&gate.left_id)?.clone();
                        self.write_single_gate(
                            &gate.left_id,
                            &input_gate,
                            wire_of_gate,
                            const_of_wire,
                        )?;
                    }
                    if wire_of_gate.get(&gate.right_id).is_none() {
                        let input_gate = self.c_ref.get_gate(&gate.right_id)?.clone();
                        self.write_single_gate(
                            &gate.right_id,
                            &input_gate,
                            wire_of_gate,
                            const_of_wire,
                        )?;
                    }
                }
                NXAOBoolGate::Or(gate) => {
                    if wire_of_gate.get(&gate.left_id).is_none() {
                        let input_gate = self.c_ref.get_gate(&gate.left_id)?.clone();
                        self.write_single_gate(
                            &gate.left_id,
                            &input_gate,
                            wire_of_gate,
                            const_of_wire,
                        )?;
                    }
                    if wire_of_gate.get(&gate.right_id).is_none() {
                        let input_gate = self.c_ref.get_gate(&gate.right_id)?.clone();
                        self.write_single_gate(
                            &gate.right_id,
                            &input_gate,
                            wire_of_gate,
                            const_of_wire,
                        )?;
                    }
                }
                NXAOBoolGate::Module(gate) => {
                    let input_ids = gate.input_ids;
                    for id in &input_ids {
                        if wire_of_gate.get(id).is_none() {
                            let input_gate = self.c_ref.get_gate(id)?.clone();
                            self.write_single_gate(&id, &input_gate, wire_of_gate, const_of_wire)?;
                        }
                    }
                }
            }
        }

        for i in 0..output_len {
            let gate_id = output_gate_ids[i];
            let gate = &output_gates[i];
            if wire_of_gate.get(&gate_id).is_none() {
                self.write_single_gate(&gate_id, gate, wire_of_gate, const_of_wire)?;
            }
        }
        Ok(())
    }

    fn write_single_gate(
        &mut self,
        gate_id: &GateId,
        gate: &NXAOBoolGate,
        wire_of_gate: &mut HashMap<GateId, usize>,
        const_of_wire: &mut HashMap<usize, bool>,
    ) -> Result<(), BristolError> {
        match gate {
            NXAOBoolGate::Input(gate) => {
                self.update_wire(gate_id, 0, None, &gate.to_str(), wire_of_gate)
            }
            NXAOBoolGate::Const(_) => Ok(()),
            NXAOBoolGate::Not(gate) => {
                if wire_of_gate.get(&gate.id).is_none() {
                    //println!("not found id {}",gate.id);
                    let input_gate = self.c_ref.get_gate(&gate.id)?.clone();
                    self.write_single_gate(&gate.id, &input_gate, wire_of_gate, const_of_wire)?;
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
                    //println!("not found id {}",gate.left_id);
                    let input_gate = self.c_ref.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(
                        &gate.left_id,
                        &input_gate,
                        wire_of_gate,
                        const_of_wire,
                    )?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    //println!("not found id {}",gate.right_id);
                    let input_gate = self.c_ref.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(
                        &gate.right_id,
                        &input_gate,
                        wire_of_gate,
                        const_of_wire,
                    )?;
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
                    //println!("not found id {}",gate.left_id);
                    let input_gate = self.c_ref.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(
                        &gate.left_id,
                        &input_gate,
                        wire_of_gate,
                        const_of_wire,
                    )?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    //println!("not found id {}",gate.right_id);
                    let input_gate = self.c_ref.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(
                        &gate.right_id,
                        &input_gate,
                        wire_of_gate,
                        const_of_wire,
                    )?;
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
                    //println!("not found id {}",gate.left_id);
                    let input_gate = self.c_ref.get_gate(&gate.left_id)?.clone();
                    self.write_single_gate(
                        &gate.left_id,
                        &input_gate,
                        wire_of_gate,
                        const_of_wire,
                    )?;
                }
                if wire_of_gate.get(&gate.right_id).is_none() {
                    //println!("not found id {}",gate.right_id);
                    let input_gate = self.c_ref.get_gate(&gate.right_id)?.clone();
                    self.write_single_gate(
                        &gate.right_id,
                        &input_gate,
                        wire_of_gate,
                        const_of_wire,
                    )?;
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
                //println!("writer module id {} gate id {}",gate.module_id, gate_id);
                let input_ids = &gate.input_ids;
                for id in input_ids {
                    if wire_of_gate.get(id).is_none() {
                        let input_gate = self.c_ref.get_gate(id)?.clone();
                        self.write_single_gate(&id, &input_gate, wire_of_gate, const_of_wire)?;
                    }
                }
                let module_circuit = self.c_ref.get_module(&gate.module_id)?.clone();
                let mut new_wire_of_gate = HashMap::new();
                let mut last_input_wire_id = WireId(0);
                let mut i = 0;
                while i < input_ids.len() {
                    let gate_id = module_circuit.input_to_gate_id(&last_input_wire_id)?;
                    match gate_id {
                        Some(id) => {
                            let my_gate_id = input_ids[i];
                            new_wire_of_gate.insert(id, wire_of_gate[&my_gate_id]);
                            i += 1;
                        }
                        None => {}
                    };
                    last_input_wire_id += WireId(1);
                }

                let cur_c_ref = self.c_ref.clone();
                self.c_ref = module_circuit.clone();
                self.write_all_gates(&mut new_wire_of_gate, const_of_wire)?;
                self.c_ref = cur_c_ref;
                let first_output_id = GateId(gate_id.0 - (gate.out_index as u64));
                for i in 0..gate.output_len() {
                    let output_wire_id = WireId(i as u64);
                    let output_gate_id = module_circuit.output_to_gate_id(&output_wire_id)?.clone();
                    let my_gate_id = GateId(first_output_id.0 + (i as u64));
                    wire_of_gate.insert(my_gate_id, new_wire_of_gate[&output_gate_id]);
                }
                /*let sub_buf_writer = BufWriter::new(&mut self.writer);
                let mut sub_writer = BristolNXAOWriter::new(module_circuit, sub_buf_writer);
                sub_writer.num_wire = self.num_wire;
                sub_writer.write_all_gates(wire_of_gate)?;*/
                //self.writer.write_all(&sub_writer.writer.get_ref())?;
                Ok(())
            }
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
                self.writer.write_all(write_str.as_bytes())?;
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
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id = circuit.input().unwrap();
        let not = circuit.not(&input_gate_id).unwrap();
        circuit.output(not).unwrap();
        let c_ref = circuit.to_ref();

        let buf_writer = BufWriter::new(Vec::new());
        let mut writer = BristolNXAOWriter::new(c_ref.clone(), buf_writer);
        writer.write(None).unwrap();
        //println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let vec = writer.writer.into_inner().unwrap();
        let buf_read = BufReader::new(&vec[..]);
        let mut read_circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        reader.read(buf_read, &mut read_circuit).unwrap();
        assert_eq!(c_ref, read_circuit);
    }

    #[test]
    fn xor_test() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let not = circuit.xor(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(not).unwrap();
        let c_ref = circuit.to_ref();

        let buf_writer = BufWriter::new(Vec::new());
        let mut writer = BristolNXAOWriter::new(c_ref.clone(), buf_writer);
        writer.write(None).unwrap();
        //println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let vec = writer.writer.into_inner().unwrap();
        let buf_read = BufReader::new(&vec[..]);
        let mut read_circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        reader.read(buf_read, &mut read_circuit).unwrap();
        assert_eq!(c_ref, read_circuit);
    }

    #[test]
    fn and_test() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let not = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(not).unwrap();
        let c_ref = circuit.to_ref();

        let buf_writer = BufWriter::new(Vec::new());
        let mut writer = BristolNXAOWriter::new(c_ref.clone(), buf_writer);
        writer.write(None).unwrap();
        //println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let vec = writer.writer.into_inner().unwrap();
        let buf_read = BufReader::new(&vec[..]);
        let mut read_circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        reader.read(buf_read, &mut read_circuit).unwrap();
        assert_eq!(c_ref, read_circuit);
    }

    #[test]
    fn or_test() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let not = circuit.or(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(not).unwrap();
        let c_ref = circuit.to_ref();

        let buf_writer = BufWriter::new(Vec::new());
        let mut writer = BristolNXAOWriter::new(c_ref.clone(), buf_writer);
        writer.write(None).unwrap();
        //println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let vec = writer.writer.into_inner().unwrap();
        let buf_read = BufReader::new(&vec[..]);
        let mut read_circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        reader.read(buf_read, &mut read_circuit).unwrap();
        assert_eq!(c_ref, read_circuit);
    }

    #[test]
    fn module_1_test() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let mut eq_circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let eq_input_gate_id1 = eq_circuit.input().unwrap();
        let eq_input_gate_id2 = eq_circuit.input().unwrap();
        let eq_xor = eq_circuit
            .xor(&eq_input_gate_id1, &eq_input_gate_id2)
            .unwrap();
        let eq_not = eq_circuit.not(&eq_xor).unwrap();
        eq_circuit.output(eq_not).unwrap();
        let eq_module_id = circuit.register_module(&eq_circuit.to_ref());
        let call_inputs = [input_gate_id1, input_gate_id2];
        let eq_call = circuit.module(&eq_module_id, &call_inputs).unwrap();
        circuit.output(eq_call[0]).unwrap();
        let c_ref = circuit.to_ref();

        let buf_writer = BufWriter::new(Vec::new());
        let mut writer = BristolNXAOWriter::new(c_ref.clone(), buf_writer);
        writer.write(None).unwrap();
        //println!("{}", writer.writer);
        let mut reader = BristolNXAOReader::new();
        let vec = writer.writer.into_inner().unwrap();
        let buf_read = BufReader::new(&vec[..]);
        let mut read_circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        let read_result = reader.read(buf_read, &mut read_circuit);
        assert!(read_result.is_ok());
    }
}
