use crate::bool_circuit::*;
use crate::bristol_converter::*;
use crate::circuits::{build_circuit_from_bristol, BuildCircuitError};
use crate::gates::*;
use std::ops::{Not,BitAnd,BitOr,BitXor,BitAndAssign,BitOrAssign,BitXorAssign};

#[derive(Debug, Clone)]
pub struct AllocBits<G: Gate, C: BoolCircuit<G>, const N:usize> {
    pub bits: Vec<GateId>,
    pub c_ref: BoolCircuitRef<G,C>,
    not_mid: ModuleId,
    and_mid: ModuleId,
    or_mid: ModuleId,
    xor_mid: ModuleId
}

impl<G: Gate, C: BoolCircuit<G>,const N:usize> AllocBits<G,C,N> {
    pub fn new(mut c_ref: BoolCircuitRef<G,C>, not_mid: ModuleId, and_mid: ModuleId, or_mid: ModuleId,xor_mid: ModuleId) -> Result<Self,BuildCircuitError> {
        let mut bits = Vec::new();
        for _ in 0..N {
            bits.push(c_ref.input()?);
        }
        Ok(Self {
            bits,
            c_ref,
            not_mid,
            and_mid,
            or_mid,
            xor_mid
        })
    }

    pub fn output(&self) -> Result<(),BuildCircuitError> {
        let mut c_ref = self.c_ref.clone();
        for i in 0..N {
            c_ref.output(self.bits[i])?;
        }
        Ok(())
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> Not for &'a AllocBits<G,C,N> {
    type Output = AllocBits<G,C,N>;
    fn not(self) -> Self::Output {
        let mut new_ref = self.c_ref.clone();
        let inputs = &self.bits[..];
        let outputs = new_ref.module(&self.not_mid, inputs).expect("AllocBits Not Error");
        AllocBits {
            bits: outputs,
            c_ref: new_ref,
            not_mid: self.not_mid,
            and_mid: self.and_mid,
            or_mid: self.or_mid,
            xor_mid: self.xor_mid
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>,const N:usize> BitAnd<&'b AllocBits<G,C,N>> for &'a AllocBits<G,C,N> {
    type Output = AllocBits<G,C,N>;
    fn bitand(self, other: &'b AllocBits<G,C,N>) -> Self::Output {
        let mut new_ref = self.c_ref.clone();
        let inputs = [&self.bits[..],&other.bits[..]].concat();
        let outputs = new_ref.module(&self.and_mid, &inputs).expect("AllocBits And Error");
        AllocBits {
            bits: outputs,
            c_ref: new_ref,
            not_mid: self.not_mid,
            and_mid: self.and_mid,
            or_mid: self.or_mid,
            xor_mid: self.xor_mid
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>,const N:usize> BitOr<&'b AllocBits<G,C,N>> for &'a AllocBits<G,C,N> {
    type Output = AllocBits<G,C,N>;
    fn bitor(self, other: &'b AllocBits<G,C,N>) -> Self::Output {
        let mut new_ref = self.c_ref.clone();
        let inputs = [&self.bits[..],&other.bits[..]].concat();
        let outputs = new_ref.module(&self.or_mid, &inputs).expect("AllocBits Or Error");
        AllocBits {
            bits: outputs,
            c_ref: new_ref,
            not_mid: self.not_mid,
            and_mid: self.and_mid,
            or_mid: self.or_mid,
            xor_mid: self.xor_mid
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>,const N:usize> BitXor<&'b AllocBits<G,C,N>> for &'a AllocBits<G,C,N> {
    type Output = AllocBits<G,C,N>;
    fn bitxor(self, other: &'b AllocBits<G,C,N>) -> Self::Output {
        let mut new_ref = self.c_ref.clone();
        let inputs = [&self.bits[..],&other.bits[..]].concat();
        let outputs = new_ref.module(&self.xor_mid, &inputs).expect("AllocBits Xor Error");
        AllocBits {
            bits: outputs,
            c_ref: new_ref,
            not_mid: self.not_mid,
            and_mid: self.and_mid,
            or_mid: self.or_mid,
            xor_mid: self.xor_mid
        }
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> BitAndAssign<&'a AllocBits<G,C,N>> for AllocBits<G,C,N> {
    fn bitand_assign(&mut self, other:&'a AllocBits<G,C,N>) {
        let inputs = [&self.bits[..],&other.bits[..]].concat();
        self.bits = self.c_ref.module(&self.and_mid,&inputs).expect("AllocBits AndAssign Error");
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> BitOrAssign<&'a AllocBits<G,C,N>> for AllocBits<G,C,N> {
    fn bitor_assign(&mut self, other:&'a AllocBits<G,C,N>) {
        let inputs = [&self.bits[..],&other.bits[..]].concat();
        self.bits = self.c_ref.module(&self.or_mid,&inputs).expect("AllocBits OrAssign Error");
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> BitXorAssign<&'a AllocBits<G,C,N>> for AllocBits<G,C,N> {
    fn bitxor_assign(&mut self, other:&'a AllocBits<G,C,N>) {
        let inputs = [&self.bits[..],&other.bits[..]].concat();
        self.bits = self.c_ref.module(&self.xor_mid,&inputs).expect("AllocBits XorAssign Error");
    }
}


pub fn build_not_circuit<G: Gate, C: BoolCircuit<G>>(n_bits:usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut inputs = Vec::new();
    for _ in 0..n_bits {
        inputs.push(circuit.input()?);
    }
    for i in 0..n_bits {
        let out = circuit.not(&inputs[i])?;
        circuit.output(out)?;
    }
    Ok(circuit)
}

pub fn build_and_circuit<G: Gate, C: BoolCircuit<G>>(n_bits:usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }
    for i in 0..n_bits {
        let out = circuit.and(&a_inputs[i], &b_inputs[i])?;
        circuit.output(out)?;
    }
    Ok(circuit)
}

pub fn build_or_circuit<G: Gate, C: BoolCircuit<G>>(n_bits:usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }
    for i in 0..n_bits {
        let out = circuit.or(&a_inputs[i], &b_inputs[i])?;
        circuit.output(out)?;
    }
    Ok(circuit)
}

pub fn build_xor_circuit<G: Gate, C: BoolCircuit<G>>(n_bits:usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }
    for i in 0..n_bits {
        let out = circuit.xor(&a_inputs[i], &b_inputs[i])?;
        circuit.output(out)?;
    }
    Ok(circuit)
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::*;
    use rand::Rng;

    #[test]
    fn not() {
        let mut circuit = NXAOBoolCircuit::new();
        let not_circuit = build_not_circuit(256).unwrap();
        let and_circuit = build_and_circuit(256).unwrap();
        let or_circuit = build_or_circuit(256).unwrap();
        let xor_circuit = build_xor_circuit(256).unwrap();
        let not_mid = circuit.register_module(not_circuit);
        let and_mid = circuit.register_module(and_circuit);
        let or_mid = circuit.register_module(or_circuit);
        let xor_mid = circuit.register_module(xor_circuit);
        let c_ref = circuit.to_ref();
        let bits = AllocBits::<_,_,256>::new(c_ref.clone(),not_mid,and_mid,or_mid,xor_mid).unwrap();
        let outs = !(&bits);
        outs.output().unwrap();
        
        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs = [false;256];
        for i in 0..256 {
            inputs[i] = rng.gen();
        }
        let output = evaluator.eval_output(&inputs).unwrap();
        for i in 0..256 {
            assert_eq!(output[i],!inputs[i]);
        }
    }

    #[test]
    fn and() {
        let mut circuit = NXAOBoolCircuit::new();
        let not_circuit = build_not_circuit(256).unwrap();
        let and_circuit = build_and_circuit(256).unwrap();
        let or_circuit = build_or_circuit(256).unwrap();
        let xor_circuit = build_xor_circuit(256).unwrap();
        let not_mid = circuit.register_module(not_circuit);
        let and_mid = circuit.register_module(and_circuit);
        let or_mid = circuit.register_module(or_circuit);
        let xor_mid = circuit.register_module(xor_circuit);
        let c_ref = circuit.to_ref();
        let bits_l = AllocBits::<_,_,256>::new(c_ref.clone(),not_mid,and_mid,or_mid,xor_mid).unwrap();
        let bits_r = AllocBits::<_,_,256>::new(c_ref.clone(),not_mid,and_mid,or_mid,xor_mid).unwrap();
        let outs = (&bits_l) & (&bits_r);
        outs.output().unwrap();
        
        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs_l = [false;256];
        let mut inputs_r = [false;256];
        for i in 0..256 {
            inputs_l[i] = rng.gen();
            inputs_r[i] = rng.gen();
        }
        let inputs = [inputs_l,inputs_r].concat();
        let output = evaluator.eval_output(&inputs).unwrap();
        for i in 0..256 {
            assert_eq!(output[i],inputs_l[i] & inputs_r[i]);
        }
    }

    #[test]
    fn or() {
        let mut circuit = NXAOBoolCircuit::new();
        let not_circuit = build_not_circuit(256).unwrap();
        let and_circuit = build_and_circuit(256).unwrap();
        let or_circuit = build_or_circuit(256).unwrap();
        let xor_circuit = build_xor_circuit(256).unwrap();
        let not_mid = circuit.register_module(not_circuit);
        let and_mid = circuit.register_module(and_circuit);
        let or_mid = circuit.register_module(or_circuit);
        let xor_mid = circuit.register_module(xor_circuit);
        let c_ref = circuit.to_ref();
        let bits_l = AllocBits::<_,_,256>::new(c_ref.clone(),not_mid,and_mid,or_mid,xor_mid).unwrap();
        let bits_r = AllocBits::<_,_,256>::new(c_ref.clone(),not_mid,and_mid,or_mid,xor_mid).unwrap();
        let outs = (&bits_l) | (&bits_r);
        outs.output().unwrap();
        
        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs_l = [false;256];
        let mut inputs_r = [false;256];
        for i in 0..256 {
            inputs_l[i] = rng.gen();
            inputs_r[i] = rng.gen();
        }
        let inputs = [inputs_l,inputs_r].concat();
        let output = evaluator.eval_output(&inputs).unwrap();
        for i in 0..256 {
            assert_eq!(output[i],inputs_l[i] | inputs_r[i]);
        }
    }

    #[test]
    fn xor() {
        let mut circuit = NXAOBoolCircuit::new();
        let not_circuit = build_not_circuit(256).unwrap();
        let and_circuit = build_and_circuit(256).unwrap();
        let or_circuit = build_or_circuit(256).unwrap();
        let xor_circuit = build_xor_circuit(256).unwrap();
        let not_mid = circuit.register_module(not_circuit);
        let and_mid = circuit.register_module(and_circuit);
        let or_mid = circuit.register_module(or_circuit);
        let xor_mid = circuit.register_module(xor_circuit);
        let c_ref = circuit.to_ref();
        let bits_l = AllocBits::<_,_,256>::new(c_ref.clone(),not_mid,and_mid,or_mid,xor_mid).unwrap();
        let bits_r = AllocBits::<_,_,256>::new(c_ref.clone(),not_mid,and_mid,or_mid,xor_mid).unwrap();
        let outs = (&bits_l) ^ (&bits_r);
        outs.output().unwrap();
        
        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs_l = [false;256];
        let mut inputs_r = [false;256];
        for i in 0..256 {
            inputs_l[i] = rng.gen();
            inputs_r[i] = rng.gen();
        }
        let inputs = [inputs_l,inputs_r].concat();
        let output = evaluator.eval_output(&inputs).unwrap();
        for i in 0..256 {
            assert_eq!(output[i],inputs_l[i] ^ inputs_r[i]);
        }
    }
}