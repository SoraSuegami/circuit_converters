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
    fn circuit(&self) -> &BoolCircuitRef<G, C>;
    fn eval_output(&mut self, inputs: &[bool]) -> Result<Vec<bool>, EvaluatorError>;
}

#[derive(Debug, Clone)]
pub struct NXAOBoolEvaluator {
    pub circuit: BoolCircuitRef<NXAOBoolGate, NXAOBoolCircuit>,
}

impl BoolEvaluator<NXAOBoolGate, NXAOBoolCircuit> for NXAOBoolEvaluator {
    fn circuit(&self) -> &BoolCircuitRef<NXAOBoolGate, NXAOBoolCircuit> {
        &self.circuit
    }

    fn eval_output(&mut self, inputs: &[bool]) -> Result<Vec<bool>, EvaluatorError> {
        let circuit = self.circuit();
        let output_len = circuit.output_len();
        let mut outputs = Vec::new();
        let mut evaled_map = HashMap::<GateId, bool>::new();
        let mut last_input_wire_id = WireId(0);
        let mut i = 0;
        while i < inputs.len() {
            let gate_id = circuit.input_to_gate_id(&last_input_wire_id)?;
            match gate_id {
                Some(id) => {
                    evaled_map.insert(id, inputs[i]);
                    i += 1;
                }
                None => {}
            };
            last_input_wire_id += WireId(1);
        }

        for i in 0..output_len {
            let wire_id = WireId(i as u64);
            let output = self.eval_single_output(inputs, &wire_id, Some(&mut evaled_map))?;
            outputs.push(output);
        }
        Ok(outputs)
    }
}

impl NXAOBoolEvaluator {
    pub fn new(circuit: BoolCircuitRef<NXAOBoolGate, NXAOBoolCircuit>) -> Self {
        Self { circuit }
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
        self.eval_single_gate(inputs, &output_gate_id, &output_gate, evaled_map)?;
        let output_bit = evaled_map
            .get(&output_gate_id)
            .ok_or(EvaluatorError::UnknownEvaledBit(output_gate_id))?;
        Ok(*output_bit)
    }

    fn eval_single_gate(
        &self,
        inputs: &[bool],
        gate_id: &GateId,
        gate: &NXAOBoolGate,
        evaled_map: &mut HashMap<GateId, bool>,
    ) -> Result<(), EvaluatorError> {
        match gate {
            NXAOBoolGate::Input(_) => Ok(()),
            NXAOBoolGate::Const(gate) => {
                evaled_map.insert(*gate_id, gate.value);
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
                let mut input_bits: Vec<bool> = Vec::new();
                for id in &input_ids {
                    if evaled_map.get(id).is_none() {
                        let input_gate = self.circuit.get_gate(id)?;
                        self.eval_single_gate(inputs, id, &input_gate, evaled_map)?;
                    }
                    let val = evaled_map
                        .get(id)
                        .ok_or(EvaluatorError::UnknownEvaledBit(*id))?;
                    input_bits.push(*val);
                }
                //println!("module input bits {:?}",input_bits);
                let module_circuit = self.circuit.get_module(&gate.module_id)?;
                let mut evaluator = Self::new(module_circuit);
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
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id = circuit.input().unwrap();
        circuit.output(input_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());

        let inputs = vec![true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);

        let inputs = vec![false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);
    }

    #[test]
    fn input1_not_ouput1() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id = circuit.input().unwrap();
        let not_gate_id = circuit.not(&input_gate_id).unwrap();
        circuit.output(not_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());

        let inputs = vec![true];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], false);

        let inputs = vec![false];
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);
    }

    #[test]
    fn input_xor_output1() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let or_gate_id = circuit.xor(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(or_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());

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
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let and_gate_id = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(and_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());

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
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let or_gate_id = circuit.or(&input_gate_id1, &input_gate_id2).unwrap();
        circuit.output(or_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());

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
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let input_gate_id1 = circuit.input().unwrap();
        let input_gate_id2 = circuit.input().unwrap();
        let input_gate_id3 = circuit.input().unwrap();
        let and_gate_id = circuit.and(&input_gate_id1, &input_gate_id2).unwrap();
        let or_gate_id = circuit.or(&and_gate_id, &input_gate_id3).unwrap();
        circuit.output(or_gate_id).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());

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

        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());

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

    use crate::circuits::{arithmetic::*, cryptography::*};
    use rand::Rng;

    #[test]
    fn bristol_adder64() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        build_adder64(&mut circuit).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);
        let mut rng = rand::thread_rng();

        let input_l: [bool; 64] = [rng.gen(); 64];
        let input_r: [bool; 64] = [rng.gen(); 64];
        let input1 = [input_l, input_r].concat();
        let output1 = evaluator.eval_output(&input1).unwrap();
        let input2 = [input_r, input_l].concat();
        let output2 = evaluator.eval_output(&input2).unwrap();
        for i in 0..64 {
            assert_eq!(output1[i], output2[i]);
        }
    }

    #[test]
    fn bristol_neg64() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        build_neg64(&mut circuit).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);
        let mut rng = rand::thread_rng();

        let input: [bool; 64] = [rng.gen(); 64];
        let output1 = evaluator.eval_output(&input).unwrap();
        let output2 = evaluator.eval_output(&output1).unwrap();
        for i in 0..64 {
            assert_eq!(input[i], output2[i]);
        }
    }

    #[test]
    fn bristol_mult2_64() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        build_mult2_64(&mut circuit).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);
        let mut rng = rand::thread_rng();

        let input_l: [bool; 64] = [rng.gen(); 64];
        let input_r: [bool; 64] = [rng.gen(); 64];
        let input1 = [input_l, input_r].concat();
        let output1 = evaluator.eval_output(&input1).unwrap();
        let input2 = [input_r, input_l].concat();
        let output2 = evaluator.eval_output(&input2).unwrap();
        for i in 0..64 {
            assert_eq!(output1[i], output2[i]);
        }
    }

    /*const INIT_SHA256_STATE: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];
    /*const INIT_SHA256_STATE: [u32; 8] = [
    0x67E6096A, 0x85AE67BB, 0x72F36E3C, 0x3AF54FA5, 0x7F520E51, 0x8C68059B, 0xABD9831F, 0x19CDE05B,
    ];*/

    #[test]
    fn sha256_init() {
        let sha256_init: NXAOBoolCircuit = build_sha256_init().unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(sha256_init);
        let input1 = bytes2bits_be(&hex2bytes("00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000").unwrap()[..]);
        let output1 = evaluator.eval_output(&input1).unwrap();
        assert_eq!(bytes2hex(&bits2bytes_be(&output1[..])[..]), "da5698be17b9b46962335799779fbeca8ce5d491c0d26243bafef9ea1837a9d8");
        let input2= bytes2bits_be(&hex2bytes("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f").unwrap()[..]);
        let output2 = evaluator.eval_output(&input2).unwrap();
        assert_eq!(bytes2hex(&bits2bytes_be(&output2[..])[..]), "fc99a2df88f42a7a7bb9d18033cdc6a20256755f9d5b9a5044a9cc315abe84a7");
        let input3= bytes2bits_be(&hex2bytes("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()[..]);
        let output3 = evaluator.eval_output(&input3).unwrap();
        assert_eq!(bytes2hex(&bits2bytes_be(&output3[..])[..]), "ef0c748df4da50a8d6c43c013edc3ce76c9d9fa9a1458ade56eb86c0a64492d2");
        let input4= bytes2bits_be(&hex2bytes("243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89452821e638d01377be5466cf34e90c6cc0ac29b7c97c50dd3f84d5b5b5470917").unwrap()[..]);
        let output4 = evaluator.eval_output(&input4).unwrap();
        assert_eq!(bytes2hex(&bits2bytes_be(&output4[..])[..]), "cf0ae4eb67d38ffeb94068984b22abde4e92bc548d14585e48dca8882d7b09ce");
    }

    #[test]
    fn sha256() {
        //let mut circuit = C::new();
        let sha256_init: NXAOBoolCircuit = build_sha256_init().unwrap();
        //let sha256_module_id = circuit.register_module(sha256_inner);
        /*inputs.push(true);
        for _ in 0..(512-65-256) {
            inputs.push(false);
        }
        for i in 0..64 {
            let bit = (256u64 >> (63-i)) & 1 == 1;
            inputs.push(bit);
        }*/
        let mut inputs = Vec::new();
        for _ in 0..512 {
            inputs.push(false);
        }
        println!("inputs {:?}",inputs);
        /*for (i,num) in (0..8).zip(INIT_SHA256_STATE.into_iter()) {
            let bytes = num.to_be_bytes();
            println!("i {} bytes {:?}",i,bytes);
            let bits = bytes2bits_be(&bytes);
            let mut tmp_bits = Vec::new();
            for (j,bit) in (0..32).zip(bits.into_iter()) {
                inputs.push(bit);
                tmp_bits.push(bit)
            }
            println!("i {}, tmp_value {:?}",i,tmp_bits);
        }*/
        let mut evaluator = NXAOBoolEvaluator::new(sha256_init);
        let output = evaluator.eval_output(&inputs).unwrap();
        println!("out1 {:?}",output);
        //let output_bytes = bits2bytes_be(&output);
        //println!("{}",hex::encode(&output_bytes[..]));
        let sha256_comp = build_sha256_compression().unwrap();
        let mut new_inputs = Vec::new();
        new_inputs.push(true);
        for _ in 0..(512-65) {
            new_inputs.push(false);
        }
        for i in 0..64 {
            let bit = (512u64 >> (63-i)) & 1 == 1;
            new_inputs.push(bit);
        }
        println!("new inputs {:?}",new_inputs);
        for out in output {
            new_inputs.push(out);
        }
        let mut evaluator = NXAOBoolEvaluator::new(sha256_comp);
        let last_output = evaluator.eval_output(&new_inputs).unwrap();
        println!("{:?}",last_output);
        let output_bytes = bits2bytes_be(&last_output);
        println!("{}",hex::encode(&output_bytes[..]));
    }*/

    /*#[test]
    fn sha256() {
        let circuit = build_sha256(512).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);
        let mut rng = rand::thread_rng();
        let inputs = [false; 512];
        let output = evaluator.eval_output(&inputs).unwrap();
        println!("output {:?}",output);
        let output_bytes = bits2bytes_le(&output);
        let mut hasher = Sha256::new();
        let test_inputs = [false; 512];
        let input_bytes = bits2bytes_le(&test_inputs);
        hasher.update(&input_bytes);
        let result = hasher.finalize();
        assert_eq!(hex::encode(&output_bytes[..]), hex::encode(&result[..]));
    }*/

    #[test]
    fn aes128() {
        let mut circuit = NXAOBoolCircuit::new(ModuleStorageRef::new()).to_ref();
        build_aes128(&mut circuit).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit);
        let mut rng = rand::thread_rng();
        let key: [bool; 128] = [rng.gen(); 128];
        let msg: [bool; 128] = [rng.gen(); 128];
        let enc_input = [key, msg].concat();
        let _ = evaluator.eval_output(&enc_input).unwrap();
    }
}
