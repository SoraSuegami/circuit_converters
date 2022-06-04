use crate::*;
use std::ops::{Add,Sub,Mul,AddAssign,SubAssign,MulAssign};

#[derive(Debug, Clone)]
pub struct AllocInt<G: Gate, C: BoolCircuit<G>, const N:usize> {
    // little endian value
    pub val_le: Vec<GateId>,
    pub c_ref: BoolCircuitRef<G,C>,
    adder_mid: ModuleId,
    suber_mid: ModuleId,
    muler_mid: ModuleId
}

impl<G: Gate, C: BoolCircuit<G>,const N:usize> AllocInt<G,C,N> {
    pub fn new(mut c_ref: BoolCircuitRef<G,C>, adder_mid: ModuleId, suber_mid: ModuleId, muler_mid: ModuleId) -> Result<Self,BuildCircuitError> {
        let mut val_le = Vec::new();
        for _ in 0..N {
            val_le.push(c_ref.input()?);
        }
        Ok(Self {
            val_le,
            c_ref,
            adder_mid,
            suber_mid,
            muler_mid
        })
    }

    pub fn output(&self) -> Result<(),BuildCircuitError> {
        let mut c_ref = self.c_ref.clone();
        for i in 0..N {
            c_ref.output(self.val_le[i])?;
        }
        Ok(())
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>,const N:usize> Add<&'b AllocInt<G,C,N>> for &'a AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn add(self, other:&'b AllocInt<G,C,N>) -> Self::Output {
        let mut new_ref = self.c_ref.clone();
        let inputs = [&self.val_le[..],&other.val_le[..]].concat();
        let added_bits = new_ref.module(&self.adder_mid,&inputs).expect("AllocInt Add Error");
        AllocInt {
            val_le: added_bits,
            c_ref: new_ref,
            adder_mid: self.adder_mid,
            suber_mid: self.suber_mid,
            muler_mid: self.muler_mid
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>,const N:usize> Sub<&'b AllocInt<G,C,N>> for &'a AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn sub(self, other:&'b AllocInt<G,C,N>) -> Self::Output {
        let mut new_ref = self.c_ref.clone();
        let inputs = [&self.val_le[..],&other.val_le[..]].concat();
        let subed_bits = new_ref.module(&self.suber_mid,&inputs).expect("AllocInt Sub Error");
        AllocInt {
            val_le: subed_bits,
            c_ref: new_ref,
            adder_mid: self.adder_mid,
            suber_mid: self.suber_mid,
            muler_mid: self.muler_mid
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>,const N:usize> Mul<&'b AllocInt<G,C,N>> for &'a AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn mul(self, other:&'b AllocInt<G,C,N>) -> Self::Output {
        let mut new_ref = self.c_ref.clone();
        let inputs = [&self.val_le[..],&other.val_le[..]].concat();
        let muled_bits = new_ref.module(&self.muler_mid,&inputs).expect("AllocInt Mul Error");
        AllocInt {
            val_le: muled_bits,
            c_ref: new_ref,
            adder_mid: self.adder_mid,
            suber_mid: self.suber_mid,
            muler_mid: self.muler_mid
        }
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> AddAssign<&'a AllocInt<G,C,N>> for AllocInt<G,C,N> {
    fn add_assign(&mut self, other:&'a AllocInt<G,C,N>) {
        let inputs = [&self.val_le[..],&other.val_le[..]].concat();
        self.val_le = self.c_ref.module(&self.adder_mid,&inputs).expect("AllocInt AddAssign Error");
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> SubAssign<&'a AllocInt<G,C,N>> for AllocInt<G,C,N> {
    fn sub_assign(&mut self, other:&'a AllocInt<G,C,N>) {
        let inputs = [&self.val_le[..],&other.val_le[..]].concat();
        self.val_le = self.c_ref.module(&self.suber_mid,&inputs).expect("AllocInt SubAssign Error");
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> MulAssign<&'a AllocInt<G,C,N>> for AllocInt<G,C,N> {
    fn mul_assign(&mut self, other:&'a AllocInt<G,C,N>) {
        let inputs = [&self.val_le[..],&other.val_le[..]].concat();
        self.val_le = self.c_ref.module(&self.muler_mid,&inputs).expect("AllocInt MulAssign Error");
    }
}


pub fn build_add_circuit<G: Gate, C: BoolCircuit<G>>(n_bits:usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }
    let mut gs = Vec::new();
    let mut ps = Vec::new();
    for i in 0..n_bits {
        let a = a_inputs[i];
        let b = b_inputs[i];
        let g = circuit.and(&a,&b)?;
        let p = circuit.or(&a,&b)?;
        gs.push(g);
        ps.push(p);
    }
    let mut cs = Vec::new();
    cs.push(gs[0]);
    for i in 1..n_bits {
        let pc_pre = circuit.and(&ps[i],&cs[i-1])?;
        let c = circuit.or(&gs[i],&pc_pre)?;
        cs.push(c);
    }
    let first_s = circuit.xor(&a_inputs[0],&b_inputs[0])?;
    circuit.output(first_s)?;
    for i in 1..n_bits {
        let a_xor_b = circuit.xor(&a_inputs[i],&b_inputs[i])?;
        let s = circuit.xor(&a_xor_b, &cs[i-1])?;
        circuit.output(s)?;
    }
    Ok(circuit)
}

pub fn build_sub_circuit<G: Gate, C: BoolCircuit<G>>(n_bits:usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let add_circuit:C = build_add_circuit(n_bits)?;
    let add_mid = circuit.register_module(add_circuit);

    let mut b_fliped = Vec::new();
    for i in 0..n_bits {
        b_fliped.push(circuit.not(&b_inputs[i])?);
    }
    b_fliped.push(circuit.constant(true)?);
    for _ in 1..n_bits {
        b_fliped.push(circuit.constant(false)?);
    }
    let mut comp_b = circuit.module(&add_mid, &b_fliped)?;
    a_inputs.append(&mut comp_b);
    let results = circuit.module(&add_mid, &a_inputs)?;
    for result in results.into_iter() {
        circuit.output(result)?;
    }
    Ok(circuit)
}

pub fn build_mul_circuit<G: Gate, C: BoolCircuit<G>>(n_bits:usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let add_circuit:C = build_add_circuit(n_bits)?;
    let add_mid = circuit.register_module(add_circuit);

    let mut sum = Vec::with_capacity(n_bits);
    for _ in 0..n_bits {
        let zero = circuit.constant(false)?;
        sum.push(zero);
    }

    for i in 0..n_bits {
        let mut andeds = Vec::new();
        for _ in 0..i {
            let zero = circuit.constant(false)?;
            andeds.push(zero);
        }
        for j in 0..(n_bits-i) {
            let and = circuit.and(&a_inputs[j],&b_inputs[i])?;
            andeds.push(and);
        }
        let inputs = [sum,andeds].concat();
        sum = circuit.module(&add_mid, &inputs)?;
    }

    for i in 0..n_bits {
        circuit.output(sum[i])?;
    }
    Ok(circuit)
}


pub fn build_mul_extend_circuit<G: Gate, C: BoolCircuit<G>>(n_bits:usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let add_circuit:C = build_add_circuit(2*n_bits)?;
    let add_mid = circuit.register_module(add_circuit);

    let mut sum = Vec::with_capacity(2*n_bits);
    for _ in 0..2*n_bits {
        let zero = circuit.constant(false)?;
        sum.push(zero);
    }

    for i in 0..n_bits {
        let mut andeds = Vec::new();
        for _ in 0..i {
            let zero = circuit.constant(false)?;
            andeds.push(zero);
        }
        for j in 0..n_bits {
            let and = circuit.and(&a_inputs[j],&b_inputs[i])?;
            andeds.push(and);
        }
        for _ in 0..(n_bits-i) {
            let zero = circuit.constant(false)?;
            andeds.push(zero);
        }
        let inputs = [sum,andeds].concat();
        sum = circuit.module(&add_mid, &inputs)?;
    }

    for i in 0..2*n_bits {
        circuit.output(sum[i])?;
    }
    Ok(circuit)
}


#[cfg(test)]
mod test {
    use super::*;

    use crate::circuits::{arithmetic::*, cryptography::*};
    use rand::Rng;

    #[test]
    fn adder() {
        let circuit:NXAOBoolCircuit = build_add_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());
        let mut rng = rand::thread_rng();

        let mut input_l: [bool; 256] = [false;256];
        let mut input_r: [bool; 256] = [false;256];
        for i in 0..256 {
            input_l[i] = rng.gen();
            input_r[i] = rng.gen();
        }
        let input1 = [input_l, input_r].concat();
        let output1 = evaluator.eval_output(&input1).unwrap();
        let input2 = [input_r, input_l].concat();
        let output2 = evaluator.eval_output(&input2).unwrap();
        for i in 0..256 {
            assert_eq!(output1[i], output2[i]);
        }
    }

    #[test]
    fn suber() {
        let sub_circuit:NXAOBoolCircuit = build_sub_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(sub_circuit.to_ref());
        let mut rng = rand::thread_rng();

        let mut input_l: [bool; 256] = [false;256];
        let mut input_r: [bool; 256] = [false;256];
        for i in 0..256 {
            input_l[i] = rng.gen();
            input_r[i] = rng.gen();
        }
        let input1 = [input_l, input_r].concat();
        let output1 = evaluator.eval_output(&input1).unwrap();

        let add_circuit = build_add_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(add_circuit);
        let input2 = [input_r.to_vec(), output1].concat();
        let output2 = evaluator.eval_output(&input2).unwrap();
        for i in 0..256 {
            assert_eq!(input_l[i], output2[i]);
        }
    }

    #[test]
    fn muler() {
        let mul_circuit:NXAOBoolCircuit = build_mul_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(mul_circuit.to_ref());
        let mut rng = rand::thread_rng();

        let mut input_l: [bool; 256] = [false;256];
        let mut input_r: [bool; 256] = [false;256];
        for i in 0..128 {
            input_l[i] = rng.gen();
            input_r[i] = rng.gen();
        }
        let input1 = [input_l, input_r].concat();
        let output1 = evaluator.eval_output(&input1).unwrap();
        let input2 = [input_r, input_l].concat();
        let output2 = evaluator.eval_output(&input2).unwrap();
        for i in 0..256 {
            assert_eq!(output1[i], output2[i]);
        }
    }

    #[test]
    fn muler_extend() {
        let mul_circuit:NXAOBoolCircuit = build_mul_extend_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(mul_circuit.to_ref());
        let mut rng = rand::thread_rng();

        let mut input_l: [bool; 256] = [false;256];
        let mut input_r: [bool; 256] = [false;256];
        for i in 0..256 {
            input_l[i] = rng.gen();
            input_r[i] = rng.gen();
        }
        let input1 = [input_l, input_r].concat();
        let output1 = evaluator.eval_output(&input1).unwrap();
        let input2 = [input_r, input_l].concat();
        let output2 = evaluator.eval_output(&input2).unwrap();
        for i in 0..512 {
            assert_eq!(output1[i], output2[i]);
        }
    }

    #[test]
    fn alloc_int() {
        let mut circuit = NXAOBoolCircuit::new();
        let add_circuit = build_add_circuit(256).unwrap();
        let sub_circuit = build_sub_circuit(256).unwrap();
        let mul_circuit = build_mul_circuit(256).unwrap();
        let add_mid = circuit.register_module(add_circuit);
        let sub_mid = circuit.register_module(sub_circuit);
        let mul_mid = circuit.register_module(mul_circuit);
        let c_ref = circuit.to_ref();
        let int1 = AllocInt::<_,_,256>::new(c_ref.clone(),add_mid,sub_mid,mul_mid).unwrap();
        let int2 = AllocInt::<_,_,256>::new(c_ref.clone(),add_mid,sub_mid,mul_mid).unwrap();
        let int3 = AllocInt::<_,_,256>::new(c_ref.clone(),add_mid,sub_mid,mul_mid).unwrap();
        let out1 = &(&int1 - &int2) * &int3;
        let out2 = &(&int1*&int3) -  &(&int2*&int3);
        let mut c_ref = out2.c_ref;
        for i in 0..256 {
            let eq = c_ref.eq(&out1.val_le[i], &out2.val_le[i]).unwrap();
            c_ref.output(eq).unwrap();
        }

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs = [false;256*3];
        for i in 0..(256*3) {
            inputs[i] = rng.gen();
        }
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output,vec![true;256]);
        
    }

}
