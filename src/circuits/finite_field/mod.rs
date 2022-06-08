use crate::bool_circuit::*;
use crate::circuits::{arithmetic::*, BuildCircuitError};
use crate::gates::*;
use num_bigint::BigUint;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

#[derive(Debug, Clone)]
pub struct AllocFp<G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize> {
    pub val: AllocInt<G, C, N>,
    pub config: AllocFpConfig<G, C, N, REXP>,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize> AllocFp<G, C, N, REXP> {
    pub fn new(config: &AllocFpConfig<G, C, N, REXP>) -> Result<Self, BuildCircuitError> {
        let config = config.clone();
        let val = AllocInt::new(&config.int_config)?;
        Ok(Self { val, config })
    }

    pub fn from_gate_ids_unchecked(
        val: Vec<GateId>,
        config: &AllocFpConfig<G, C, N, REXP>,
    ) -> Self {
        let val = AllocInt::from_gate_ids(val, &config.int_config)
            .expect("Alloc Fp from_gate_ids_unchecked Error");
        Self {
            val,
            config: config.clone(),
        }
    }

    pub fn from_biguint_unchecked(val: &BigUint, config: &AllocFpConfig<G, C, N, REXP>) -> Self {
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

    pub fn zero(config: &AllocFpConfig<G, C, N, REXP>) -> Result<Self, BuildCircuitError> {
        let val = AllocInt::zero(&config.int_config)?;
        Ok(Self {
            val,
            config: config.clone(),
        })
    }

    pub fn one(config: &AllocFpConfig<G, C, N, REXP>) -> Result<Self, BuildCircuitError> {
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

    /*pub fn less(&self, other: &Self) -> Result<GateId, BuildCircuitError> {
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
            new_val_le.push(self.val_le[i-shift_bits]);
        }
        let new_int = Self {
            val_le: new_val_le,
            config
        };
        Ok(new_int)
    }

    pub fn shift_right(&self, shift_bits: usize) -> Result<Self, BuildCircuitError> {
        let config = self.config.clone();
        let mut new_val_le = Vec::new();
        let sign_bit = self.val_le[N-1];
        for i in 0..(N-shift_bits) {
            new_val_le.push(self.val_le[i+shift_bits]);
        }
        for _ in (N-shift_bits)..N {
            new_val_le.push(sign_bit);
        }
        let new_int = Self {
            val_le: new_val_le,
            config
        };
        Ok(new_int)
    }*/
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize> Neg
    for &'a AllocFp<G, C, N, REXP>
{
    type Output = AllocFp<G, C, N, REXP>;
    fn neg(self) -> Self::Output {
        let zero = AllocFp::zero(&self.config).expect("Alloc Neg Error");
        &zero - self
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize>
    Add<&'b AllocFp<G, C, N, REXP>> for &'a AllocFp<G, C, N, REXP>
{
    type Output = AllocFp<G, C, N, REXP>;
    fn add(self, other: &'b AllocFp<G, C, N, REXP>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = new_ref
            .module(&self.config.add_mid, &inputs)
            .expect("AllocFp Add Error");
        AllocFp::from_gate_ids_unchecked(out_bits, &config)
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize>
    Sub<&'b AllocFp<G, C, N, REXP>> for &'a AllocFp<G, C, N, REXP>
{
    type Output = AllocFp<G, C, N, REXP>;
    fn sub(self, other: &'b AllocFp<G, C, N, REXP>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = new_ref
            .module(&self.config.sub_mid, &inputs)
            .expect("AllocFp Sub Error");
        AllocFp::from_gate_ids_unchecked(out_bits, &config)
    }
}

impl<'a, 'b, G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize>
    Mul<&'b AllocFp<G, C, N, REXP>> for &'a AllocFp<G, C, N, REXP>
{
    type Output = AllocFp<G, C, N, REXP>;
    fn mul(self, other: &'b AllocFp<G, C, N, REXP>) -> Self::Output {
        let mut config = self.config.clone();
        let new_ref = &mut config.c_ref;
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = new_ref
            .module(&self.config.mul_mid, &inputs)
            .expect("AllocFp Mul Error");
        AllocFp::from_gate_ids_unchecked(out_bits, &config)
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize>
    AddAssign<&'a AllocFp<G, C, N, REXP>> for AllocFp<G, C, N, REXP>
{
    fn add_assign(&mut self, other: &'a AllocFp<G, C, N, REXP>) {
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = self
            .config
            .c_ref
            .module(&self.config.add_mid, &inputs)
            .expect("AllocFp AddAssign Error");
        self.val = AllocFp::from_gate_ids_unchecked(out_bits, &self.config).val;
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize>
    SubAssign<&'a AllocFp<G, C, N, REXP>> for AllocFp<G, C, N, REXP>
{
    fn sub_assign(&mut self, other: &'a AllocFp<G, C, N, REXP>) {
        let inputs = [&self.to_gate_ids()[..], &other.to_gate_ids()[..]].concat();
        let out_bits = self
            .config
            .c_ref
            .module(&self.config.sub_mid, &inputs)
            .expect("AllocFp SubAssign Error");
        self.val = AllocFp::from_gate_ids_unchecked(out_bits, &self.config).val;
    }
}

impl<'a, G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize>
    MulAssign<&'a AllocFp<G, C, N, REXP>> for AllocFp<G, C, N, REXP>
{
    fn mul_assign(&mut self, other: &'a AllocFp<G, C, N, REXP>) {
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
pub struct AllocFpConfig<G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize> {
    pub c_ref: BoolCircuitRef<G, C>,
    pub int_config: AllocIntConfig<G, C, N>,
    pub p: BigUint,
    pub p_minus_inv: BigUint,
    pub r2: BigUint,
    pub add_mid: ModuleId,
    pub sub_mid: ModuleId,
    pub mul_mid: ModuleId,
}

impl<G: Gate, C: BoolCircuit<G>, const N: usize, const REXP: usize> AllocFpConfig<G, C, N, REXP> {
    pub fn new(
        c_ref: &BoolCircuitRef<G, C>,
        p: BigUint,
        p_minus_inv: BigUint,
        r2: BigUint,
    ) -> Result<Self, BuildCircuitError> {
        let mut c_ref = c_ref.clone();
        let int_config = AllocIntConfig::new(&c_ref)?;
        let adder = Self::build_add_circuit(&p)?;
        let add_mid = c_ref.register_module(adder);
        let suber = Self::build_sub_circuit(&p)?;
        let sub_mid = c_ref.register_module(suber);
        let muler = Self::build_mul_circuit(&p, &p_minus_inv, &r2)?;
        let mul_mid = c_ref.register_module(muler);
        Ok(Self {
            c_ref,
            int_config,
            p,
            p_minus_inv,
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
    ) -> Result<BoolCircuitRef<G, C>, BuildCircuitError> {
        let circuit = C::new();
        let mut c_ref = circuit.to_ref();
        let int_config = AllocIntConfig::<G, C, N>::new(&c_ref)?;
        let l = AllocInt::new(&int_config)?;
        let r = AllocInt::new(&int_config)?;
        let lr = (&l) * (&r);
        let p_int = AllocInt::from_biguint(p, &int_config)?;
        let p_minus_inv_int = AllocInt::from_biguint(p_minus_inv, &int_config)?;
        let lr_mod = Self::mont_red(&lr, &mut c_ref, &int_config, &p_int, &p_minus_inv_int)?;
        let r2_int = AllocInt::from_biguint(r2, &int_config)?;
        let lr_mod_r2 = (&lr_mod) * (&r2_int);
        let out = Self::mont_red(
            &lr_mod_r2,
            &mut c_ref,
            &int_config,
            &p_int,
            &p_minus_inv_int,
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
    ) -> Result<AllocInt<G, C, N>, BuildCircuitError> {
        // val * p_minus_inv
        let mut val_pi = val * p_minus_inv_int;
        let false_bit = c_ref.constant(false)?;
        // (val * p_minus_inv) mod R
        for i in REXP..N {
            val_pi.val_le[i] = c_ref.and(&val_pi.val_le[i], &false_bit)?;
        }
        // ((val * p_minus_inv) mod R) * p
        let val_pi_p = (&val_pi) * p_int;
        // val + ((val * p_minus_inv) mod R) * p
        let val_val_pi_p = val + (&val_pi_p);
        // t = (val + ((val * p_minus_inv) mod R) * p) / r
        let t = val_val_pi_p.shift_right(REXP)?;
        let is_larger_or_eq = t.larger_or_eq(&p_int)?;
        let is_larger_or_eq_int = AllocInt::from_gate_ids(vec![is_larger_or_eq], int_config)?;
        let else_int = (&AllocInt::one(&int_config)?) - (&is_larger_or_eq_int);
        let p_subed_t = (&t) - p_int;
        let out = &(&is_larger_or_eq_int * &p_subed_t) - &(&else_int * &t);
        Ok(out)
    }

    /*fn to_mont_exp(val: &AllocInt<G,C,N>, c_ref: &mut BoolCircuitRef<G,C>, int_config: &AllocIntConfig<G,C,N>, p_int:&AllocInt<G,C,N>, p_minus_inv_int:&AllocInt<G,C,N>, r2:&AllocInt<G,C,N>) -> Result<AllocInt<G,C,N>, BuildCircuitError> {
        let val = val * r2;
        Self::mont_red(&val, c_ref, int_config, p_int, p_minus_inv_int)
    }*/
}
