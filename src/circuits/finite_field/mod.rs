use crate::{bool_circuit::*, ext_gcd};
use crate::circuits::{arithmetic::*, BuildCircuitError};
use crate::gates::*;
use num_bigint::{BigUint, BigInt};
use num_traits::Zero;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

#[derive(Debug, Clone)]
pub struct AllocFp<G: Gate, C: BoolCircuit<G>, const N: usize> {
    pub val: AllocInt<G, C, N>,
    pub config: AllocFpConfig<G, C, N>,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize> AllocFp<G, C, N> {
    pub fn new(config: &AllocFpConfig<G, C, N>) -> Result<Self, BuildCircuitError> {
        let config = config.clone();
        let val = AllocInt::new(&config.int_config)?;
        Ok(Self { val, config })
    }

    pub fn from_gate_ids_unchecked(val: Vec<GateId>, config: &AllocFpConfig<G, C, N>) -> Self {
        let val = AllocInt::from_gate_ids(val, &config.int_config)
            .expect("Alloc Fp from_gate_ids_unchecked Error");
        Self {
            val,
            config: config.clone(),
        }
    }

    pub fn from_biguint_unchecked(val: &BigUint, config: &AllocFpConfig<G, C, N>) -> Self {
        let val = AllocInt::from_biguint(val, &config.int_config)
            .expect("Alloc Fp from_biguint_unchecked Error");
        Self {
            val,
            config: config.clone(),
        }
    }

    pub fn output(&self) -> Result<(), BuildCircuitError> {
        self.val.output()
    }

    pub fn to_gate_ids(&self) -> Vec<GateId> {
        self.val.val_le.to_vec()
    }

    pub fn zero(config: &AllocFpConfig<G, C, N>) -> Result<Self, BuildCircuitError> {
        let val = AllocInt::zero(&config.int_config)?;
        Ok(Self {
            val,
            config: config.clone(),
        })
    }

    pub fn one(config: &AllocFpConfig<G, C, N>) -> Result<Self, BuildCircuitError> {
        let val = AllocInt::one(&config.int_config)?;
        Ok(Self {
            val,
            config: config.clone(),
        })
    }

    pub fn eq(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        self.val.eq(&other.val)
    }

    pub fn neq(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
        self.val.neq(&other.val)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> Neg for &'a AllocFp<G, C, N> {
    type Output = AllocFp<G, C, N>;
    fn neg(self) -> Self::Output {
        let zero = AllocFp::zero(&self.config).expect("Alloc Neg Error");
        &zero - self
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> Add<&'b AllocFp<G, C, N>>
    for &'a AllocFp<G, C, N>
{
    type Output = AllocFp<G, C, N>;
    fn add(self, other: &'b AllocFp<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = new_ref
            .module(&self.config.add_mid, &inputs)
            .expect("AllocFp Add Error");
        AllocFp::from_gate_ids_unchecked(out_bits, &config)
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> Sub<&'b AllocFp<G, C, N>>
    for &'a AllocFp<G, C, N>
{
    type Output = AllocFp<G, C, N>;
    fn sub(self, other: &'b AllocFp<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = new_ref
            .module(&self.config.sub_mid, &inputs)
            .expect("AllocFp Sub Error");
        AllocFp::from_gate_ids_unchecked(out_bits, &config)
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize> Mul<&'b AllocFp<G, C, N>>
    for &'a AllocFp<G, C, N>
{
    type Output = AllocFp<G, C, N>;
    fn mul(self, other: &'b AllocFp<G, C, N>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = new_ref
            .module(&self.config.mul_mid, &inputs)
            .expect("AllocFp Mul Error");
        AllocFp::from_gate_ids_unchecked(out_bits, &config)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> AddAssign<&'a AllocFp<G, C, N>>
    for AllocFp<G, C, N>
{
    fn add_assign(&mut self, other: &'a AllocFp<G, C, N>) {
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = self
            .config
            .c_ref
            .module(&self.config.add_mid, &inputs)
            .expect("AllocFp AddAssign Error");
        self.val = AllocFp::from_gate_ids_unchecked(out_bits, &self.config).val;
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> SubAssign<&'a AllocFp<G, C, N>>
    for AllocFp<G, C, N>
{
    fn sub_assign(&mut self, other: &'a AllocFp<G, C, N>) {
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = self
            .config
            .c_ref
            .module(&self.config.sub_mid, &inputs)
            .expect("AllocFp SubAssign Error");
        self.val = AllocFp::from_gate_ids_unchecked(out_bits, &self.config).val;
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize> MulAssign<&'a AllocFp<G, C, N>>
    for AllocFp<G, C, N>
{
    fn mul_assign(&mut self, other: &'a AllocFp<G, C, N>) {
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = self
            .config
            .c_ref
            .module(&self.config.mul_mid, &inputs)
            .expect("AllocFp MulAssign Error");
        self.val = AllocFp::from_gate_ids_unchecked(out_bits, &self.config).val;
    }
}

#[derive(Debug, Clone)]
pub struct AllocFpConfig<G: Gate, C: BoolCircuit<G>, const N: usize> {
    pub c_ref: BoolCircuitRef<G, C>,
    pub int_config: AllocIntConfig<G, C, N>,
    pub p: BigUint,
    pub p_minus_inv: BigUint,
    pub r_exp: usize,
    pub r2: BigUint,
    pub add_mid: ModuleId,
    pub sub_mid: ModuleId,
    pub mul_mid: ModuleId,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize> AllocFpConfig<G, C, N> {
    pub fn new(
        c_ref: &BoolCircuitRef<G, C>,
        p: BigUint,
        r_exp: usize,
    ) -> Result<Self, BuildCircuitError> {
        let r = BigUint::from(1u32) << r_exp;
        let r2 = ((&r) * (&r)) % (&r);
        let p_inv = Self::mod_inv(p.clone(), r.clone());
        let p_minus_inv = (&r) - (&p_inv);
        let mut c_ref = c_ref.clone();
        let int_config = AllocIntConfig::new(&c_ref)?;
        let adder = Self::build_add_circuit(&p)?;
        let add_mid = c_ref.register_module(adder);
        let suber = Self::build_sub_circuit(&p)?;
        let sub_mid = c_ref.register_module(suber);
        let muler = Self::build_mul_circuit(&p, &p_minus_inv, &r2, r_exp)?;
        let mul_mid = c_ref.register_module(muler);
        Ok(Self {
            c_ref,
            int_config,
            p,
            p_minus_inv,
            r_exp,
            r2,
            add_mid,
            sub_mid,
            mul_mid,
        })
    }

    fn build_add_circuit(p: &BigUint) -> Result<BoolCircuitRef<G, C>, BuildCircuitError> {
        let circuit = C::new();
        let mut c_ref = circuit.to_ref();
        let int_config = AllocIntConfig::<G, C, N>::new(&c_ref)?;
        let l = AllocInt::new(&int_config)?;
        let r = AllocInt::new(&int_config)?;

        let p_int = AllocInt::from_biguint(p, &int_config)?;

        let sum = (&l) + (&r);
        let is_plus_larger = sum.larger(&p_int)?;
        let is_plus_larger_int = AllocInt::from_gate_ids(vec![is_plus_larger], &int_config)?;
        let is_minus_less = sum.less(&(-&AllocInt::zero(&int_config)?))?;
        let is_minus_less_int = AllocInt::from_gate_ids(vec![is_minus_less], &int_config)?;
        let else_bit = c_ref.or(&is_plus_larger, &is_minus_less)?;
        let else_bit = c_ref.not(&else_bit)?;
        let else_int = AllocInt::from_gate_ids(vec![else_bit], &int_config)?;

        let out = &((&is_plus_larger_int) * &(&sum - &p_int))
            + &((&is_minus_less_int) * &(&sum + &p_int));
        let out = &out + &(&else_int * &sum);
        out.output()?;
        Ok(c_ref)
    }

    fn build_sub_circuit(p: &BigUint) -> Result<BoolCircuitRef<G, C>, BuildCircuitError> {
        let circuit = C::new();
        let mut c_ref = circuit.to_ref();
        let adder = Self::build_add_circuit(p)?;
        let add_mid = c_ref.register_module(adder);
        let int_config = AllocIntConfig::<G, C, N>::new(&c_ref)?;
        let l = AllocInt::new(&int_config)?;
        let r = AllocInt::new(&int_config)?;

        let r = -&r;
        let inputs = [l.val_le, r.val_le].concat();
        let output = c_ref.module(&add_mid, &inputs)?;
        for i in 0..N {
            c_ref.output(output[i])?;
        }
        Ok(c_ref)
    }

    fn build_mul_circuit(
        p: &BigUint,
        p_minus_inv: &BigUint,
        r2: &BigUint,
        r_exp: usize,
    ) -> Result<BoolCircuitRef<G, C>, BuildCircuitError> {
        let circuit = C::new();
        let mut c_ref = circuit.to_ref();
        let int_config = AllocIntConfig::<G, C, N>::new(&c_ref)?;
        let l = AllocInt::new(&int_config)?;
        let r = AllocInt::new(&int_config)?;
        let lr = (&l) * (&r);
        let p_int = AllocInt::from_biguint(p, &int_config)?;
        let p_minus_inv_int = AllocInt::from_biguint(p_minus_inv, &int_config)?;
        let lr_mod = Self::mont_red(
            &lr,
            &mut c_ref,
            &int_config,
            &p_int,
            &p_minus_inv_int,
            r_exp,
        )?;
        let r2_int = AllocInt::from_biguint(r2, &int_config)?;
        let lr_mod_r2 = (&lr_mod) * (&r2_int);
        let out = Self::mont_red(
            &lr_mod_r2,
            &mut c_ref,
            &int_config,
            &p_int,
            &p_minus_inv_int,
            r_exp,
        )?;
        out.output()?;
        Ok(c_ref)
    }

    fn mont_red(
        val: &AllocInt<G, C, N>,
        c_ref: &mut BoolCircuitRef<G, C>,
        int_config: &AllocIntConfig<G, C, N>,
        p_int: &AllocInt<G, C, N>,
        p_minus_inv_int: &AllocInt<G, C, N>,
        r_exp: usize,
    ) -> Result<AllocInt<G, C, N>, BuildCircuitError> {
        // val * p_minus_inv
        let mut val_pi = val * p_minus_inv_int;
        let false_bit = c_ref.constant(false)?;
        // (val * p_minus_inv) mod R
        for i in r_exp..N {
            val_pi.val_le[i] = c_ref.and(&val_pi.val_le[i], &false_bit)?;
        }
        // ((val * p_minus_inv) mod R) * p
        let val_pi_p = (&val_pi) * p_int;
        // val + ((val * p_minus_inv) mod R) * p
        let val_val_pi_p = val + (&val_pi_p);
        // t = (val + ((val * p_minus_inv) mod R) * p) / r
        let t = val_val_pi_p.shift_right(r_exp)?;
        let is_larger_or_eq = t.larger_or_eq(&p_int)?;
        let is_larger_or_eq_int = AllocInt::from_gate_ids(vec![is_larger_or_eq], int_config)?;
        let else_int = (&AllocInt::one(&int_config)?) - (&is_larger_or_eq_int);
        let p_subed_t = (&t) - p_int;
        let out = &(&is_larger_or_eq_int * &p_subed_t) - &(&else_int * &t);
        Ok(out)
    }

    fn mod_inv(val:BigUint, p:BigUint) -> BigUint {
        let a = BigInt::from(val);
        let b = BigInt::from(p);
        let (x,_,_) = ext_gcd(&a, &b);
        let (_, bytes_le) = if x < BigInt::zero() {
            (x + b).to_bytes_le()
        } else {
            x.to_bytes_le()
        };
        BigUint::from_bytes_le(&bytes_le)
    }

    /*fn to_mont_exp(val: &AllocInt<G,C,N>, c_ref: &mut BoolCircuitRef<G,C>, int_config: &AllocIntConfig<G,C,N>, p_int:&AllocInt<G,C,N>, p_minus_inv_int:&AllocInt<G,C,N>, r2:&AllocInt<G,C,N>) -> Result<AllocInt<G,C,N>, BuildCircuitError> {
        let val = val * r2;
        Self::mont_red(&val, c_ref, int_config, p_int, p_minus_inv_int)
    }*/
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::*;
    use hex;
    use rand::Rng;

    #[test]
    fn fp_add() {
        let p = BigUint::parse_bytes(b"11", 10).unwrap();
        const REXP:usize = 4;
        const N:usize = 2*REXP;

        let circuit = NXAOBoolCircuit::new();
        let mut c_ref = circuit.to_ref();
        let config = AllocFpConfig::<_,_,N>::new(&c_ref,p,REXP).unwrap();
        let int1 = AllocFp::<_, _, N>::new(&config).unwrap();
        let int2 = AllocFp::<_, _, N>::new(&config).unwrap();
        let int3 = AllocFp::<_, _, N>::new(&config).unwrap();
        let out1 = &(&int1 - &int2) * &int3;
        let out2 = &(&int1 * &int3) - &(&int2 * &int3);
        let eq = out1.eq(&out2).unwrap();
        c_ref.output(eq).unwrap();

        let mut evaluator = NXAOBoolEvaluator::new(c_ref);
        let mut rng = rand::thread_rng();
        let mut inputs = [false; N * 3];
        for i in 0..(N * 3) {
            inputs[i] = rng.gen();
        }
        let output = evaluator.eval_output(&inputs).unwrap()[0];
        assert_eq!(output, true);
    }
}
