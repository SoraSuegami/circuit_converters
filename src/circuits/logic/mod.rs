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
    pub fn new(
        mut c_ref: BoolCircuitRef<G, C>,
        config: &AllocBitsConfig<G, C, N>,
    ) -> Result<Self, BuildCircuitError> {
        let mut bits = Vec::new();
        for _ in 0..N {
            bits.push(c_ref.input()?);
        }
        Ok(Self {
            bits,
            config: config.clone(),
        })
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
        let not = build_not_circuit(N)?;
        let not_mid = c_ref.register_module(not);
        let and = build_and_circuit(N)?;
        let and_mid = c_ref.register_module(and);
        let or = build_or_circuit(N)?;
        let or_mid = c_ref.register_module(or);
        let xor = build_xor_circuit(N)?;
        let xor_mid = c_ref.register_module(xor);
        let eq = build_eq_circuit(N)?;
        let eq_mid = c_ref.register_module(eq);
        let neq = build_neq_circuit(N)?;
        let neq_mid = c_ref.register_module(neq);
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
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
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

pub fn build_and_circuit<G: Gate, C: BoolCircuit<G>>(
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
    for i in 0..n_bits {
        let out = circuit.and(&a_inputs[i], &b_inputs[i])?;
        circuit.output(out)?;
    }
    Ok(circuit)
}

pub fn build_or_circuit<G: Gate, C: BoolCircuit<G>>(n_bits: usize) -> Result<C, BuildCircuitError> {
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

pub fn build_xor_circuit<G: Gate, C: BoolCircuit<G>>(
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
    for i in 0..n_bits {
        let out = circuit.xor(&a_inputs[i], &b_inputs[i])?;
        circuit.output(out)?;
    }
    Ok(circuit)
}

pub fn build_eq_circuit<G: Gate, C: BoolCircuit<G>>(n_bits: usize) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let mut a_inputs = Vec::new();
    let mut b_inputs = Vec::new();
    for _ in 0..n_bits {
        a_inputs.push(circuit.input()?);
    }
    for _ in 0..n_bits {
        b_inputs.push(circuit.input()?);
    }

    let mut eq_bit = circuit.constant(true)?;
    for i in 0..n_bits {
        let is_eq = circuit.eq(&a_inputs[i], &b_inputs[i])?;
        eq_bit = circuit.and(&eq_bit, &is_eq)?;
    }
    circuit.output(eq_bit)?;
    Ok(circuit)
}

pub fn build_neq_circuit<G: Gate, C: BoolCircuit<G>>(
    n_bits: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
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
    let eq_bit = circuit.module(&eq_mid, &inputs)?[0];
    let neq_bit = circuit.not(&eq_bit)?;
    circuit.output(neq_bit)?;
    Ok(circuit)
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::*;
    use rand::Rng;

    #[test]
    fn not() {
        let circuit = NXAOBoolCircuit::new();
        let c_ref = circuit.to_ref();
        let config = AllocBitsConfig::new(&c_ref).unwrap();
        let bits = AllocBits::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
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
        let circuit = NXAOBoolCircuit::new();
        let c_ref = circuit.to_ref();
        let config = AllocBitsConfig::new(&c_ref).unwrap();
        let bits_l = AllocBits::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
        let bits_r = AllocBits::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
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
        let circuit = NXAOBoolCircuit::new();
        let c_ref = circuit.to_ref();
        let config = AllocBitsConfig::new(&c_ref).unwrap();
        let bits_l = AllocBits::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
        let bits_r = AllocBits::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
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
        let circuit = NXAOBoolCircuit::new();
        let c_ref = circuit.to_ref();
        let config = AllocBitsConfig::new(&c_ref).unwrap();
        let bits_l = AllocBits::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
        let bits_r = AllocBits::<_, _, 256>::new(c_ref.clone(), &config).unwrap();
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
