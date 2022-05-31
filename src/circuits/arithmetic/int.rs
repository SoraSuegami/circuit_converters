use crate::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Int {
    // little endian value
    val_le: Vec<bool>
}

impl Int {
    pub fn new(val_le:Vec<bool>) -> Self {
        Self {
            val_le
        }
    }
}

impl From<&[u8]> for Int {
    fn from(val:&[u8]) -> Self {
        let bits = bytes2bits_le(val);
        Self {
            val_le: bits
        }
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

