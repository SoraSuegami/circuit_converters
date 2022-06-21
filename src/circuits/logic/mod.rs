use crate::bool_circuit::*;
use crate::circuits::BuildCircuitError;
use crate::gates::*;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

#[derive(Debug, Clone)]
pub struct AllocBits<G: Gate, C: BoolCircuit<G>, const N: usize> {
    pub bits: Vec<GateId>,
    pub config: AllocBitsConfig<G, C, N>,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize> AllocBits<G, C, N> {
    pub fn new(config: &AllocBitsConfig<G, C, N>) -> Result<Self, BuildCircuitError> {
        let mut config = config.clone();
        let new_ref = &mut config.c_ref;
        let mut bits = Vec::new();
        for _ in 0..N {
            bits.push(new_ref.input()?);
        }
        Ok(Self {
            bits,
            config: config.clone(),
        })
    }

    pub fn from_gate_ids(
        bits: Vec<GateId>,
        config: &AllocBitsConfig<G, C, N>,
    ) -> Result<Self, BuildCircuitError> {
        assert!(bits.len() <= N);
        let config = config.clone();
        let mut config = config.clone();
        let new_ref = &mut config.c_ref;
        let mut bits = bits;
        for _ in 0..(N - bits.len()) {
            bits.push(new_ref.constant(false)?);
        }
        Ok(Self { bits, config })
    }

    pub fn output(&self) -> Result<(), BuildCircuitError> {
        let mut c_ref = self.config.c_ref.clone();
        for i in 0..N {
            c_ref.output(self.bits[i])?;
        }
        Ok(())
    }

    pub fn eq(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.bits[..], &other.bits[..]].concat();
        let eq_bit = new_ref.module(&self.config.eq_mid, &inputs)?[0];
        Ok(eq_bit)
    }

    pub fn neq(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.bits[..], &other.bits[..]].concat();
        let neq_bit = new_ref.module(&self.config.neq_mid, &inputs)?[0];
        Ok(neq_bit)
    }

    pub fn mux(&self, true_bits: &Self, select_bit: &GateId) -> Result<Self, BuildCircuitError> {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let mut selected_bits = Vec::new();
        let not_s = new_ref.not(select_bit)?;
        for i in 0..N {
            let false_bit = new_ref.and(&self.bits[i],&not_s)?;
            let true_bit = new_ref.and(&true_bits.bits[i], &select_bit)?;
            selected_bits.push(new_ref.xor(&false_bit, &true_bit)?);
        }
        Ok(Self {
            bits: selected_bits,
            config
        })
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> Not for &'a AllocBits<G, C, N> {
    type Output = AllocBits<G, C, N>;
    fn not(self) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = &self.bits[..];
        let outputs = new_ref
            .module(&self.config.not_mid, inputs)
            .expect("AllocBits Not Error");
        AllocBits {
            bits: outputs,
            config,
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> BitAnd<&'b AllocBits<G, C, N>>
    for &'a AllocBits<G, C, N>
{
    type Output = AllocBits<G, C, N>;
    fn bitand(self, other: &'b AllocBits<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.bits[..], &other.bits[..]].concat();
        let outputs = new_ref
            .module(&self.config.and_mid, &inputs)
            .expect("AllocBits And Error");
        AllocBits {
            bits: outputs,
            config,
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> BitOr<&'b AllocBits<G, C, N>>
    for &'a AllocBits<G, C, N>
{
    type Output = AllocBits<G, C, N>;
    fn bitor(self, other: &'b AllocBits<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.bits[..], &other.bits[..]].concat();
        let outputs = new_ref
            .module(&self.config.or_mid, &inputs)
            .expect("AllocBits Or Error");
        AllocBits {
            bits: outputs,
            config,
        }
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> BitXor<&'b AllocBits<G, C, N>>
    for &'a AllocBits<G, C, N>
{
    type Output = AllocBits<G, C, N>;
    fn bitxor(self, other: &'b AllocBits<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.bits[..], &other.bits[..]].concat();
        let outputs = new_ref
            .module(&self.config.xor_mid, &inputs)
            .expect("AllocBits Xor Error");
        AllocBits {
            bits: outputs,
            config,
        }
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> BitAndAssign<&'a AllocBits<G, C, N>>
    for AllocBits<G, C, N>
{
    fn bitand_assign(&mut self, other: &'a AllocBits<G, C, N>) {
        let inputs = [&self.bits[..], &other.bits[..]].concat();
        self.bits = self
            .config
            .c_ref
            .module(&self.config.and_mid, &inputs)
            .expect("AllocBits AndAssign Error");
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> BitOrAssign<&'a AllocBits<G, C, N>>
    for AllocBits<G, C, N>
{
    fn bitor_assign(&mut self, other: &'a AllocBits<G, C, N>) {
        let inputs = [&self.bits[..], &other.bits[..]].concat();
        self.bits = self
            .config
            .c_ref
            .module(&self.config.or_mid, &inputs)
            .expect("AllocBits OrAssign Error");
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> BitXorAssign<&'a AllocBits<G, C, N>>
    for AllocBits<G, C, N>
{
    fn bitxor_assign(&mut self, other: &'a AllocBits<G, C, N>) {
        let inputs = [&self.bits[..], &other.bits[..]].concat();
        self.bits = self
            .config
            .c_ref
            .module(&self.config.xor_mid, &inputs)
            .expect("AllocBits XorAssign Error");
    }
}

#[derive(Debug, Clone)]
pub struct AllocBitsConfig<G: Gate, C: BoolCircuit<G>, const N: usize> {
    pub c_ref: BoolCircuitRef<G, C>,
    pub not_mid: ModuleId,
    pub and_mid: ModuleId,
    pub or_mid: ModuleId,
    pub xor_mid: ModuleId,
    pub eq_mid: ModuleId,
    pub neq_mid: ModuleId,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize> AllocBitsConfig<G, C, N> {
    pub fn new(c_ref: &BoolCircuitRef<G, C>) -> Result<Self, BuildCircuitError> {
        let mut c_ref = c_ref.clone();
        let not_mid = build_not_circuit(&mut c_ref, N)?;
        let and_mid = build_and_circuit(&mut c_ref, N)?;
        let or_mid = build_or_circuit(&mut c_ref, N)?;
        let xor_mid = build_xor_circuit(&mut c_ref, N)?;
        let eq_mid = build_eq_circuit(&mut c_ref, N)?;
        let neq_mid = build_neq_circuit(&mut c_ref, N, eq_mid)?;
        Ok(Self {
            c_ref: c_ref,
            not_mid,
            and_mid,
            or_mid,
            xor_mid,
            eq_mid,
            neq_mid,
        })
    }
}

pub fn build_not_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
) -> Result<ModuleId, BuildCircuitError> {
    let (sub_mid, mut sub_ref) = c_ref.sub_circuit();
    let mut inputs = Vec::new();
    for _ in 0..n_bits {
        inputs.push(sub_ref.input()?);
    }
    for i in 0..n_bits {
        let out = sub_ref.not(&inputs[i])?;
        sub_ref.output(out)?;
    }
    Ok(sub_mid)
}

pub fn build_and_circuit<G: Gate, C: BoolCircuit<G>>(
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
    for i in 0..n_bits {
        let out = sub_ref.and(&a_inputs[i], &b_inputs[i])?;
        sub_ref.output(out)?;
    }
    Ok(sub_mid)
}

pub fn build_or_circuit<G: Gate, C: BoolCircuit<G>>(
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
    for i in 0..n_bits {
        let out = sub_ref.or(&a_inputs[i], &b_inputs[i])?;
        sub_ref.output(out)?;
    }
    Ok(sub_mid)
}

pub fn build_xor_circuit<G: Gate, C: BoolCircuit<G>>(
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
    for i in 0..n_bits {
        let out = sub_ref.xor(&a_inputs[i], &b_inputs[i])?;
        sub_ref.output(out)?;
    }
    Ok(sub_mid)
}

pub fn build_eq_circuit<G: Gate, C: BoolCircuit<G>>(
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

    let mut eq_bit = sub_ref.constant(true)?;
    for i in 0..n_bits {
        let is_eq = sub_ref.equivalent(&a_inputs[i], &b_inputs[i])?;
        eq_bit = sub_ref.and(&eq_bit, &is_eq)?;
    }
    sub_ref.output(eq_bit)?;
    Ok(sub_mid)
}

pub fn build_neq_circuit<G: Gate, C: BoolCircuit<G>>(
    c_ref: &mut BoolCircuitRef<G, C>,
    n_bits: usize,
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
    let eq_bit = sub_ref.module(&eq_mid, &inputs)?[0];
    let neq_bit = sub_ref.not(&eq_bit)?;
    sub_ref.output(neq_bit)?;
    Ok(sub_mid)
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::*;
    use rand::Rng;

    #[test]
    fn not() {
        let circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let c_ref = circuit.to_ref();
        let config = AllocBitsConfig::new(&c_ref).unwrap();
        let bits = AllocBits::<_, _, 256>::new(&config).unwrap();
        let outs = !(&bits);
        outs.output().unwrap();

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs = [false; 256];
        for i in 0..256 {
            inputs[i] = rng.gen();
        }
        let output = evaluator.eval_output(&inputs).unwrap();
        for i in 0..256 {
            assert_eq!(output[i], !inputs[i]);
        }
    }

    #[test]
    fn and() {
        let circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let c_ref = circuit.to_ref();
        let config = AllocBitsConfig::new(&c_ref).unwrap();
        let bits_l = AllocBits::<_, _, 256>::new(&config).unwrap();
        let bits_r = AllocBits::<_, _, 256>::new(&config).unwrap();
        let outs = (&bits_l) & (&bits_r);
        outs.output().unwrap();

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs_l = [false; 256];
        let mut inputs_r = [false; 256];
        for i in 0..256 {
            inputs_l[i] = rng.gen();
            inputs_r[i] = rng.gen();
        }
        let inputs = [inputs_l, inputs_r].concat();
        let output = evaluator.eval_output(&inputs).unwrap();
        for i in 0..256 {
            assert_eq!(output[i], inputs_l[i] & inputs_r[i]);
        }
    }

    #[test]
    fn or() {
        let circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let c_ref = circuit.to_ref();
        let config = AllocBitsConfig::new(&c_ref).unwrap();
        let bits_l = AllocBits::<_, _, 256>::new(&config).unwrap();
        let bits_r = AllocBits::<_, _, 256>::new(&config).unwrap();
        let outs = (&bits_l) | (&bits_r);
        outs.output().unwrap();

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs_l = [false; 256];
        let mut inputs_r = [false; 256];
        for i in 0..256 {
            inputs_l[i] = rng.gen();
            inputs_r[i] = rng.gen();
        }
        let inputs = [inputs_l, inputs_r].concat();
        let output = evaluator.eval_output(&inputs).unwrap();
        for i in 0..256 {
            assert_eq!(output[i], inputs_l[i] | inputs_r[i]);
        }
    }

    #[test]
    fn xor() {
        let circuit = NXAOBoolCircuit::new(ModuleStorageRef::new());
        let c_ref = circuit.to_ref();
        let config = AllocBitsConfig::new(&c_ref).unwrap();
        let bits_l = AllocBits::<_, _, 256>::new(&config).unwrap();
        let bits_r = AllocBits::<_, _, 256>::new(&config).unwrap();
        let outs = (&bits_l) ^ (&bits_r);
        outs.output().unwrap();

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs_l = [false; 256];
        let mut inputs_r = [false; 256];
        for i in 0..256 {
            inputs_l[i] = rng.gen();
            inputs_r[i] = rng.gen();
        }
        let inputs = [inputs_l, inputs_r].concat();
        let output = evaluator.eval_output(&inputs).unwrap();
        for i in 0..256 {
            assert_eq!(output[i], inputs_l[i] ^ inputs_r[i]);
        }
    }
}
