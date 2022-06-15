use crate::logic::{build_eq_circuit, build_neq_circuit};
use crate::*;
use num_bigint::BigUint;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::usize;

#[derive(Debug, Clone)]
pub struct AllocInt<G: Gate, C: BoolCircuit<G>, const N: usize> {
    // little endian value
    pub val_le: Vec<GateId>,
    pub config: AllocIntConfig<G, C, N>,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize> AllocInt<G, C, N> {
    pub fn new(config: &AllocIntConfig<G, C, N>) -> Result<Self, BuildCircuitError> {
        let mut config = config.clone();
        let new_ref = &mut config.c_ref;
        let mut val_le = Vec::new();
        for _ in 0..N {
            val_le.push(new_ref.input()?);
        }
        Ok(Self { val_le, config })
    }

    pub fn from_gate_ids(
        val_le: Vec<GateId>,
        config: &AllocIntConfig<G, C, N>,
    ) -> Result<Self, BuildCircuitError> {
        assert!(val_le.len() <= N);
        let config = config.clone();
        let mut config = config.clone();
        let new_ref = &mut config.c_ref;
        let mut val_le = val_le;
        for _ in 0..(N - val_le.len()) {
            val_le.push(new_ref.constant(false)?);
        }
        Ok(Self { val_le, config })
    }

    pub fn from_biguint(
        val: &BigUint,
        config: &AllocIntConfig<G, C, N>,
    ) -> Result<Self, BuildCircuitError> {
        let mut config = config.clone();
        let new_ref = &mut config.c_ref;
        let bytes_le = val.to_bytes_le();
        let bits_le = bytes2bits_le(&bytes_le[..]);
        assert!(bits_le.len() <= N);

        let mut val_le = Vec::new();
        for i in 0..bits_le.len() {
            val_le.push(new_ref.constant(bits_le[i])?);
        }
        for _ in 0..(N - bits_le.len()) {
            val_le.push(new_ref.constant(false)?);
        }
        Ok(Self {
            val_le,
            config: config.clone(),
        })
    }

    pub fn output(&self) -> Result<(), BuildCircuitError> {
        let mut c_ref = self.config.c_ref.clone();
        for i in 0..N {
            c_ref.output(self.val_le[i])?;
        }
        Ok(())
    }

    pub fn zero(config: &AllocIntConfig<G, C, N>) -> Result<Self, BuildCircuitError> {
        Self::from_gate_ids(vec![], config)
    }

    pub fn one(config: &AllocIntConfig<G, C, N>) -> Result<Self, BuildCircuitError> {
        let mut config = config.clone();
        let new_ref = &mut config.c_ref;
        let true_bit = new_ref.constant(true)?;
        Self::from_gate_ids(vec![true_bit], &config)
    }

    pub fn eq(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let eq_bit = new_ref.module(&self.config.eq_mid, &inputs)?[0];
        Ok(eq_bit)
    }

    pub fn neq(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let neq_bit = new_ref.module(&self.config.neq_mid, &inputs)?[0];
        Ok(neq_bit)
    }

    pub fn less(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let less_bit = new_ref.module(&self.config.less_mid, &inputs)?[0];
        Ok(less_bit)
    }

    pub fn less_or_eq(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let less_or_eq_bit = new_ref.module(&self.config.less_or_eq_mid, &inputs)?[0];
        Ok(less_or_eq_bit)
    }

    pub fn larger(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let larger_bit = new_ref.module(&self.config.larger_mid, &inputs)?[0];
        Ok(larger_bit)
    }

    pub fn larger_or_eq(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let larger_or_eq_bit = new_ref.module(&self.config.larger_or_eq_mid, &inputs)?[0];
        Ok(larger_or_eq_bit)
    }

    pub fn shift_left(&self, shift_bits: usize) -> Result<Self, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let mut new_val_le = Vec::new();
        for _ in 0..shift_bits {
            new_val_le.push(new_ref.constant(false)?);
        }
        for i in shift_bits..N {
            new_val_le.push(self.val_le[i - shift_bits]);
        }
        let new_int = Self {
            val_le: new_val_le,
            config,
        };
        Ok(new_int)
    }

    pub fn shift_right(&self, shift_bits: usize) -> Result<Self, BuildCircuitError> {
        let config = self.config.clone();
        let mut new_val_le = Vec::new();
        let sign_bit = self.val_le[N - 1];
        for i in 0..(N - shift_bits) {
            new_val_le.push(self.val_le[i + shift_bits]);
        }
        for _ in (N - shift_bits)..N {
            new_val_le.push(sign_bit);
        }
        let new_int = Self {
            val_le: new_val_le,
            config,
        };
        Ok(new_int)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> Neg for &'a AllocInt<G, C, N> {
    type Output = AllocInt<G, C, N>;
    fn neg(self) -> Self::Output {
        let zero = AllocInt::zero(&self.config).expect("Alloc Neg Error");
        &zero - self
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> Add<&'b AllocInt<G, C, N>>
    for &'a AllocInt<G, C, N>
{
    type Output = AllocInt<G, C, N>;
    fn add(self, other: &'b AllocInt<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let added_bits = new_ref
            .module(&self.config.add_mid, &inputs)
            .expect("AllocInt Add Error");
        AllocInt {
            val_le: added_bits,
            config,
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> Sub<&'b AllocInt<G, C, N>>
    for &'a AllocInt<G, C, N>
{
    type Output = AllocInt<G, C, N>;
    fn sub(self, other: &'b AllocInt<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let subed_bits = new_ref
            .module(&self.config.sub_mid, &inputs)
            .expect("AllocInt Sub Error");
        AllocInt {
            val_le: subed_bits,
            config,
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> Mul<&'b AllocInt<G, C, N>>
    for &'a AllocInt<G, C, N>
{
    type Output = AllocInt<G, C, N>;
    fn mul(self, other: &'b AllocInt<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        let muled_bits = new_ref
            .module(&self.config.mul_mid, &inputs)
            .expect("AllocInt Mul Error");
        AllocInt {
            val_le: muled_bits,
            config,
        }
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> AddAssign<&'a AllocInt<G, C, N>>
    for AllocInt<G, C, N>
{
    fn add_assign(&mut self, other: &'a AllocInt<G, C, N>) {
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        self.val_le = self
            .config
            .c_ref
            .module(&self.config.add_mid, &inputs)
            .expect("AllocInt AddAssign Error");
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> SubAssign<&'a AllocInt<G, C, N>>
    for AllocInt<G, C, N>
{
    fn sub_assign(&mut self, other: &'a AllocInt<G, C, N>) {
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        self.val_le = self
            .config
            .c_ref
            .module(&self.config.sub_mid, &inputs)
            .expect("AllocInt SubAssign Error");
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> MulAssign<&'a AllocInt<G, C, N>>
    for AllocInt<G, C, N>
{
    fn mul_assign(&mut self, other: &'a AllocInt<G, C, N>) {
        let inputs = [&self.val_le[..], &other.val_le[..]].concat();
        self.val_le = self
            .config
            .c_ref
            .module(&self.config.mul_mid, &inputs)
            .expect("AllocInt MulAssign Error");
    }
}

#[derive(Debug, Clone)]
pub struct AllocIntConfig<G: Gate, C: BoolCircuit<G>, const N: usize> {
    pub c_ref: BoolCircuitRef<G, C>,
    pub add_mid: ModuleId,
    pub sub_mid: ModuleId,
    pub mul_mid: ModuleId,
    pub eq_mid: ModuleId,
    pub neq_mid: ModuleId,
    pub less_mid: ModuleId,
    pub less_or_eq_mid: ModuleId,
    pub larger_mid: ModuleId,
    pub larger_or_eq_mid: ModuleId,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize> AllocIntConfig<G, C, N> {
    pub fn new(c_ref: &BoolCircuitRef<G, C>) -> Result<Self, BuildCircuitError> {
        let mut c_ref = c_ref.clone();
        let add_mid = build_add_circuit(&mut c_ref, N)?;
        let sub_mid = build_sub_circuit(&mut c_ref, N, add_mid)?;
        let mul_mid = build_mul_circuit(&mut c_ref, N, add_mid)?;
        let eq_mid = build_eq_circuit(&mut c_ref, N)?;
        let neq_mid = build_neq_circuit(&mut c_ref, N, eq_mid)?;
        let less_mid = build_less_circuit(&mut c_ref, N, sub_mid)?;
        let less_or_eq_mid = build_less_or_eq_circuit(&mut c_ref, N, less_mid, eq_mid)?;
        let larger_mid = build_larger_circuit(&mut c_ref, N, less_or_eq_mid)?;
        let larger_or_eq_mid = build_larger_or_eq_circuit(&mut c_ref, N, less_mid)?;
        Ok(Self {
            c_ref,
            add_mid,
            sub_mid,
            mul_mid,
            eq_mid,
            neq_mid,
            less_mid,
            less_or_eq_mid,
            larger_mid,
            larger_or_eq_mid,
        })
    }
}

pub fn build_add_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(sub_ref.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(sub_ref.input()?);
    }
    let mut gs = Vec::new();
    let mut ps = Vec::new();
    for i in 0..n_bits {
        let a = a_inputs[i];
        let b = b_inputs[i];
        let g = sub_ref.and(&a, &b)?;
        let p = sub_ref.or(&a, &b)?;
        gs.push(g);
        ps.push(p);
    }
    let mut cs = Vec::new();
    cs.push(gs[0]);
    for i in 1..n_bits {
        let pc_pre = sub_ref.and(&ps[i], &cs[i - 1])?;
        let c = sub_ref.or(&gs[i], &pc_pre)?;
        cs.push(c);
    }
    let first_s = sub_ref.xor(&a_inputs[0], &b_inputs[0])?;
    sub_ref.output(first_s)?;
    for i in 1..n_bits {
        let a_xor_b = sub_ref.xor(&a_inputs[i], &b_inputs[i])?;
        let s = sub_ref.xor(&a_xor_b, &cs[i - 1])?;
        sub_ref.output(s)?;
    }
    Ok(sub_mid)
}

pub fn build_sub_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
    add_mid: ModuleId,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(sub_ref.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(sub_ref.input()?);
    }

    let mut b_fliped = Vec::new();
    for i in 0..n_bits {
        b_fliped.push(sub_ref.not(&b_inputs[i])?);
    }
    b_fliped.push(sub_ref.constant(true)?);
    for _ in 1..n_bits {
        b_fliped.push(sub_ref.constant(false)?);
    }
    let mut comp_b = sub_ref.module(&add_mid, &b_fliped)?;
    a_inputs.append(&mut comp_b);
    let results = sub_ref.module(&add_mid, &a_inputs)?;
    for result in results.into_iter() {
        sub_ref.output(result)?;
    }
    Ok(sub_mid)
}

pub fn build_mul_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
    add_mid: ModuleId,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(sub_ref.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(sub_ref.input()?);
    }

    let mut sum = Vec::with_capacity(n_bits);
    for _ in 0..n_bits {
        let zero = sub_ref.constant(false)?;
        sum.push(zero);
    }

    for i in 0..n_bits {
        let mut andeds = Vec::new();
        for _ in 0..i {
            let zero = sub_ref.constant(false)?;
            andeds.push(zero);
        }
        for j in 0..(n_bits - i) {
            let and = sub_ref.and(&a_inputs[j], &b_inputs[i])?;
            andeds.push(and);
        }
        let inputs = [sum, andeds].concat();
        sum = sub_ref.module(&add_mid, &inputs)?;
    }

    for i in 0..n_bits {
        sub_ref.output(sum[i])?;
    }
    Ok(sub_mid)
}

pub fn build_mul_extend_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
    add_mid: ModuleId,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(sub_ref.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(sub_ref.input()?);
    }

    let mut sum = Vec::with_capacity(2 * n_bits);
    for _ in 0..2 * n_bits {
        let zero = sub_ref.constant(false)?;
        sum.push(zero);
    }

    for i in 0..n_bits {
        let mut andeds = Vec::new();
        for _ in 0..i {
            let zero = sub_ref.constant(false)?;
            andeds.push(zero);
        }
        for j in 0..n_bits {
            let and = sub_ref.and(&a_inputs[j], &b_inputs[i])?;
            andeds.push(and);
        }
        for _ in 0..(n_bits - i) {
            let zero = sub_ref.constant(false)?;
            andeds.push(zero);
        }
        let inputs = [sum, andeds].concat();
        sum = sub_ref.module(&add_mid, &inputs)?;
    }

    for i in 0..2 * n_bits {
        sub_ref.output(sum[i])?;
    }
    Ok(sub_mid)
}

pub fn build_less_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
    suber_mid: ModuleId,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(sub_ref.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(sub_ref.input()?);
    }

    let inputs = [a_inputs, b_inputs].concat();
    let sub = sub_ref.module(&suber_mid, &inputs)?;
    let one = sub_ref.constant(true)?;
    let is_less = sub_ref.equivalent(&sub[n_bits - 1], &one)?;
    sub_ref.output(is_less)?;
    Ok(sub_mid)
}

pub fn build_less_or_eq_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
    less_mid: ModuleId,
    eq_mid: ModuleId,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(sub_ref.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(sub_ref.input()?);
    }

    let inputs = [a_inputs, b_inputs].concat();
    let is_less = sub_ref.module(&less_mid, &inputs)?[0];
    let is_eq = sub_ref.module(&eq_mid, &inputs)?[0];
    let is_less_or_eq = sub_ref.or(&is_less, &is_eq)?;
    sub_ref.output(is_less_or_eq)?;
    Ok(sub_mid)
}

pub fn build_larger_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
    less_or_eq_mid: ModuleId,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(sub_ref.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(sub_ref.input()?);
    }

    let inputs = [a_inputs, b_inputs].concat();
    let is_less_or_eq = sub_ref.module(&less_or_eq_mid, &inputs)?[0];
    let is_larger = sub_ref.not(&is_less_or_eq)?;
    sub_ref.output(is_larger)?;
    Ok(sub_mid)
}

pub fn build_larger_or_eq_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
    less_mid: ModuleId,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(sub_ref.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(sub_ref.input()?);
    }

    let inputs = [a_inputs, b_inputs].concat();
    let is_less = sub_ref.module(&less_mid, &inputs)?[0];
    let is_larger_or_eq = sub_ref.not(&is_less)?;
    sub_ref.output(is_larger_or_eq)?;
    Ok(sub_mid)
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::circuits::arithmetic::*;
    use rand::Rng;

    /*#[test]
    fn adder() {
        let circuit: NXAOBoolCircuit = build_add_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(circuit.to_ref());
        let mut rng = rand::thread_rng();

        let mut input_l: [bool; 256] = [false; 256];
        let mut input_r: [bool; 256] = [false; 256];
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
        let sub_circuit: NXAOBoolCircuit = build_sub_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(sub_circuit.to_ref());
        let mut rng = rand::thread_rng();

        let mut input_l: [bool; 256] = [false; 256];
        let mut input_r: [bool; 256] = [false; 256];
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
        let mul_circuit: NXAOBoolCircuit = build_mul_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(mul_circuit.to_ref());
        let mut rng = rand::thread_rng();

        let mut input_l: [bool; 256] = [false; 256];
        let mut input_r: [bool; 256] = [false; 256];
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
        let mul_circuit: NXAOBoolCircuit = build_mul_extend_circuit(256).unwrap();
        let mut evaluator = NXAOBoolEvaluator::new(mul_circuit.to_ref());
        let mut rng = rand::thread_rng();

        let mut input_l: [bool; 256] = [false; 256];
        let mut input_r: [bool; 256] = [false; 256];
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
    }*/

    #[test]
    fn add_sub_mul_test() {
        let circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let mut c_ref = circuit.to_ref();
        let config = AllocIntConfig::new(&c_ref).unwrap();
        let int1 = AllocInt::<_, _, 256>::new(&config).unwrap();
        let int2 = AllocInt::<_, _, 256>::new(&config).unwrap();
        let int3 = AllocInt::<_, _, 256>::new(&config).unwrap();
        let out1 = &(&int1 - &int2) * &int3;
        let out2 = &(&int1 * &int3) - &(&int2 * &int3);
        let eq = out1.eq(&out2).unwrap();
        c_ref.output(eq).unwrap();

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs = [false; 256 * 3];
        for i in 0..(256 * 3) {
            inputs[i] = rng.gen();
        }
        let output = evaluator.eval_output(&inputs).unwrap()[0];
        assert_eq!(output, true);
    }

    #[test]
    fn less() {
        let circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let mut c_ref = circuit.to_ref();
        let config = AllocIntConfig::new(&c_ref).unwrap();
        let int1 = AllocInt::<_, _, 256>::new(&config).unwrap();
        let one = AllocInt::<_, _, 256>::one(&config).unwrap();
        let int2 = (&int1) + (&one);
        let is_less = int1.less(&int2).unwrap();
        let is_not_less = int2.less(&int1).unwrap();
        c_ref.output(is_less).unwrap();
        c_ref.output(is_not_less).unwrap();

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs = [false; 256];
        for i in 0..(256) {
            inputs[i] = rng.gen();
        }
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);
        assert_eq!(output[1], false);
    }

    #[test]
    fn larger() {
        let circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let mut c_ref = circuit.to_ref();
        let config = AllocIntConfig::new(&c_ref).unwrap();
        let int1 = AllocInt::<_, _, 256>::new(&config).unwrap();
        let one = AllocInt::<_, _, 256>::one(&config).unwrap();
        let int2 = (&int1) - (&one);
        let is_larger = int1.larger(&int2).unwrap();
        let is_not_larger = int2.larger(&int1).unwrap();
        c_ref.output(is_larger).unwrap();
        c_ref.output(is_not_larger).unwrap();

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs = [false; 256];
        for i in 0..(256) {
            inputs[i] = rng.gen();
        }
        let output = evaluator.eval_output(&inputs).unwrap();
        assert_eq!(output[0], true);
        assert_eq!(output[1], false);
    }
}
