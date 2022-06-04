use crate::logic::{build_eq_circuit, build_neq_circuit};
use crate::*;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use std::usize;

#[derive(Debug, Clone)]
pub struct AllocInt<G: Gate, C: BoolCircuit<G>, const N: usize> {
    // little endian value
    pub val_le: Vec<GateId>,
    pub config: AllocIntConfig<G, C, N>,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize> AllocInt<G, C, N> {
    pub fn new(
        mut c_ref: BoolCircuitRef<G, C>,
        config: &AllocIntConfig<G, C, N>,
    ) -> Result<Self, BuildCircuitError> {
        let mut val_le = Vec::new();
        for _ in 0..N {
            val_le.push(c_ref.input()?);
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

    pub fn zero(
        mut c_ref: BoolCircuitRef<G, C>,
        config: &AllocIntConfig<G, C, N>,
    ) -> Result<Self, BuildCircuitError> {
        let mut val_le = Vec::new();
        for _ in 0..N {
            val_le.push(c_ref.constant(false)?);
        }
        Ok(Self {
            val_le,
            config: config.clone(),
        })
    }

    pub fn one(
        mut c_ref: BoolCircuitRef<G, C>,
        config: &AllocIntConfig<G, C, N>,
    ) -> Result<Self, BuildCircuitError> {
        let mut val_le = Vec::new();
        val_le.push(c_ref.constant(true)?);
        for _ in 1..N {
            val_le.push(c_ref.constant(false)?);
        }
        Ok(Self {
            val_le,
            config: config.clone(),
        })
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
}

/*impl<G: Gate, C: BoolCircuit<G>,const N:usize> Add<AllocInt<G,C,N>> for AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn add(self, other:AllocInt<G,C,N>) -> Self::Output {
        (&self) + (&other)
    }
}

impl<G: Gate, C: BoolCircuit<G>,const N:usize> Sub<AllocInt<G,C,N>> for AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn sub(self, other:AllocInt<G,C,N>) -> Self::Output {
        (&self) - (&other)
    }
}

impl<G: Gate, C: BoolCircuit<G>,const N:usize> Mul<AllocInt<G,C,N>> for AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn mul(self, other:AllocInt<G,C,N>) -> Self::Output {
        (&self) * (&other)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> Add<&'a AllocInt<G,C,N>> for AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn add(self, other:&'a AllocInt<G,C,N>) -> Self::Output {
        (&self) + (other)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> Sub<&'a AllocInt<G,C,N>> for AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn sub(self, other:&'a AllocInt<G,C,N>) -> Self::Output {
        (&self) - (other)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> Mul<&'a AllocInt<G,C,N>> for AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn mul(self, other:&'a AllocInt<G,C,N>) -> Self::Output {
        (&self) * (other)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> Add<AllocInt<G,C,N>> for &'a AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn add(self, other:AllocInt<G,C,N>) -> Self::Output {
        (self) + (&other)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> Sub<AllocInt<G,C,N>> for &'a AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn sub(self, other: AllocInt<G,C,N>) -> Self::Output {
        (self) - (&other)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>,const N:usize> Mul<AllocInt<G,C,N>> for &'a AllocInt<G,C,N> {
    type Output = AllocInt<G,C,N>;
    fn mul(self, other:AllocInt<G,C,N>) -> Self::Output {
        (self) * (&other)
    }
}*/

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
        let adder = build_add_circuit(N)?;
        let add_mid = c_ref.register_module(adder);
        let suber = build_sub_circuit(N)?;
        let sub_mid = c_ref.register_module(suber);
        let muler = build_mul_circuit(N)?;
        let mul_mid = c_ref.register_module(muler);
        let eq = build_eq_circuit(N)?;
        let eq_mid = c_ref.register_module(eq);
        let neq = build_neq_circuit(N)?;
        let neq_mid = c_ref.register_module(neq);
        let less = build_less_circuit(N)?;
        let less_mid = c_ref.register_module(less);
        let less_or_eq = build_less_or_eq_circuit(N)?;
        let less_or_eq_mid = c_ref.register_module(less_or_eq);
        let larger = build_larger_circuit(N)?;
        let larger_mid = c_ref.register_module(larger);
        let larger_or_eq = build_larger_or_eq_circuit(N)?;
        let larger_or_eq_mid = c_ref.register_module(larger_or_eq);
        Ok(Self {
            c_ref: c_ref,
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
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
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
        let g = circuit.and(&a, &b)?;
        let p = circuit.or(&a, &b)?;
        gs.push(g);
        ps.push(p);
    }
    let mut cs = Vec::new();
    cs.push(gs[0]);
    for i in 1..n_bits {
        let pc_pre = circuit.and(&ps[i], &cs[i - 1])?;
        let c = circuit.or(&gs[i], &pc_pre)?;
        cs.push(c);
    }
    let first_s = circuit.xor(&a_inputs[0], &b_inputs[0])?;
    circuit.output(first_s)?;
    for i in 1..n_bits {
        let a_xor_b = circuit.xor(&a_inputs[i], &b_inputs[i])?;
        let s = circuit.xor(&a_xor_b, &cs[i - 1])?;
        circuit.output(s)?;
    }
    Ok(circuit)
}

pub fn build_sub_circuit<G: Gate, C: BoolCircuit<G>>(
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let adder = build_add_circuit(n_bits)?;
    let add_mid = circuit.register_module(adder);

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

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

pub fn build_mul_circuit<G: Gate, C: BoolCircuit<G>>(
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let adder = build_add_circuit(n_bits)?;
    let add_mid = circuit.register_module(adder);

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

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
        for j in 0..(n_bits - i) {
            let and = circuit.and(&a_inputs[j], &b_inputs[i])?;
            andeds.push(and);
        }
        let inputs = [sum, andeds].concat();
        sum = circuit.module(&add_mid, &inputs)?;
    }

    for i in 0..n_bits {
        circuit.output(sum[i])?;
    }
    Ok(circuit)
}

pub fn build_mul_extend_circuit<G: Gate, C: BoolCircuit<G>>(
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let adder = build_add_circuit(2 * n_bits)?;
    let add_mid = circuit.register_module(adder);

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let mut sum = Vec::with_capacity(2 * n_bits);
    for _ in 0..2 * n_bits {
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
            let and = circuit.and(&a_inputs[j], &b_inputs[i])?;
            andeds.push(and);
        }
        for _ in 0..(n_bits - i) {
            let zero = circuit.constant(false)?;
            andeds.push(zero);
        }
        let inputs = [sum, andeds].concat();
        sum = circuit.module(&add_mid, &inputs)?;
    }

    for i in 0..2 * n_bits {
        circuit.output(sum[i])?;
    }
    Ok(circuit)
}

pub fn build_less_circuit<G: Gate, C: BoolCircuit<G>>(
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let suber = build_sub_circuit(n_bits)?;
    let sub_mid = circuit.register_module(suber);

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let inputs = [a_inputs, b_inputs].concat();
    let sub = circuit.module(&sub_mid, &inputs)?;
    let one = circuit.constant(true)?;
    let is_less = circuit.eq(&sub[n_bits - 1], &one)?;
    circuit.output(is_less)?;
    Ok(circuit)
}

pub fn build_less_or_eq_circuit<G: Gate, C: BoolCircuit<G>>(
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let less = build_less_circuit(n_bits)?;
    let less_mid = circuit.register_module(less);
    let eq = build_eq_circuit(n_bits)?;
    let eq_mid = circuit.register_module(eq);

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let inputs = [a_inputs, b_inputs].concat();
    let is_less = circuit.module(&less_mid, &inputs)?[0];
    let is_eq = circuit.module(&eq_mid, &inputs)?[0];
    let is_less_or_eq = circuit.or(&is_less, &is_eq)?;
    circuit.output(is_less_or_eq)?;
    Ok(circuit)
}

pub fn build_larger_circuit<G: Gate, C: BoolCircuit<G>>(
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let less_or_eq = build_less_or_eq_circuit(n_bits)?;
    let less_or_eq_mid = circuit.register_module(less_or_eq);

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let inputs = [a_inputs, b_inputs].concat();
    let is_less_or_eq = circuit.module(&less_or_eq_mid, &inputs)?[0];
    let is_larger = circuit.not(&is_less_or_eq)?;
    circuit.output(is_larger)?;
    Ok(circuit)
}

pub fn build_larger_or_eq_circuit<G: Gate, C: BoolCircuit<G>>(
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let less = build_less_circuit(n_bits)?;
    let less_mid = circuit.register_module(less);

    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let inputs = [a_inputs, b_inputs].concat();
    let is_less = circuit.module(&less_mid, &inputs)?[0];
    let is_larger_or_eq = circuit.not(&is_less)?;
    circuit.output(is_larger_or_eq)?;
    Ok(circuit)
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::circuits::arithmetic::*;
    use rand::Rng;

    #[test]
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
    }

    #[test]
    fn alloc_int() {
        let circuit = NXAOBoolCircuit::new();
        let mut c_ref = circuit.to_ref();
        let config = AllocIntConfig::new(&c_ref).unwrap();
        let int1 = AllocInt::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
        let int2 = AllocInt::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
        let int3 = AllocInt::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
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
        let circuit = NXAOBoolCircuit::new();
        let mut c_ref = circuit.to_ref();
        let config = AllocIntConfig::new(&c_ref).unwrap();
        let int1 = AllocInt::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
        let one = AllocInt::<_, _, 256>::one(c_ref.clone(), &config).unwrap();
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
        let circuit = NXAOBoolCircuit::new();
        let mut c_ref = circuit.to_ref();
        let config = AllocIntConfig::new(&c_ref).unwrap();
        let int1 = AllocInt::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
        let one = AllocInt::<_, _, 256>::one(c_ref.clone(), &config).unwrap();
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
