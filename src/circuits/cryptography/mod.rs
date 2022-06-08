use crate::bool_circuit::*;
use crate::bristol_converter::*;
use crate::circuits::{build_circuit_from_bristol, BuildCircuitError};
use crate::gates::*;
//use crate::utils::*;
use std::io::BufReader;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum BuildCryptographicCircuitError {
    #[error("A next input is not found in build_sha256_without_padding.")]
    Sha256NotFoundNext,
}

//build_circuit_from_bristol!(build_aes128, "aes128_full.txt");
build_circuit_from_bristol!(build_aes128, "AES-non-expanded.txt");
//build_circuit_from_bristol!(build_sha256_init, "sha-256.txt");
//build_circuit_from_bristol!(build_sha256_compression, "sha256_compression.txt");
//build_circuit_from_bristol!(build_sha256_compression, "sha256Final.txt");

/*const INIT_SHA256_STATE: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

pub fn build_sha256<G: Gate, C: BoolCircuit<G>>(
    input_bits_len: usize,
) -> Result<C, BuildCircuitError> {
    let mut circuit = C::new();
    let sha256_inner: C = build_sha256_compression()?;
    let sha256_module_id = circuit.register_module(sha256_inner);
    let num_block = (input_bits_len + 64) / 512 + 1;

    //first chain:
    let mut first_sha256_inner: C = build_sha256_compression()?;
    for (i,num) in (0..8).zip(INIT_SHA256_STATE.into_iter()) {
        let bytes = num.to_be_bytes();
        let bits = bytes2bits_be(&bytes);
        for (j,bit) in (0..32).zip(bits.into_iter()) {
            first_sha256_inner.fix_input(&WireId(512+32*i+j), bit)?;
        }
    }
    assert_eq!(first_sha256_inner.input_len(),512);
    let first_sha256_module_id = circuit.register_module(first_sha256_inner);
    let first_inputs = (0..512).map(|_| circuit.input()).collect::<Result<Vec<_>,_>>()?;
    let mut states = circuit.module(&first_sha256_module_id, &first_inputs)?;

    //intermediate chains
    for _ in 1..(num_block-1) {
        let mut inputs = (0..512).map(|_| circuit.input()).collect::<Result<Vec<_>,_>>()?;
        inputs.append(&mut states);
        states = circuit.module(&sha256_module_id, &inputs)?;
    }

    //last chain
    let num_remain_inputs = input_bits_len % 512;
    let mut last_sha256_inner: C = build_sha256_compression()?;
    last_sha256_inner.fix_input(&WireId(num_remain_inputs as u64), true)?;
    let mut last_wire_id = WireId(num_remain_inputs as u64 + 1);
    for _ in 0..(512-num_remain_inputs-64-1) {
        last_sha256_inner.fix_input(&last_wire_id, false)?;
        last_wire_id += WireId(1);
    }
    for i in 0..64 {
        let bit = (input_bits_len >> (63-i)) & 1 == 1;
        last_sha256_inner.fix_input(&last_wire_id, bit)?;
        last_wire_id += WireId(1);
    }
    assert_eq!(last_sha256_inner.input_len(),256+num_remain_inputs);
    let last_sha256_module_id = circuit.register_module(last_sha256_inner);
    let mut last_inputs = (0..num_remain_inputs).map(|_| circuit.input()).collect::<Result<Vec<_>,_>>()?;
    last_inputs.append(&mut states);
    states = circuit.module(&last_sha256_module_id, &last_inputs)?;

    for i in 0..256 {
        circuit.output(states[i])?;
    }
    Ok(circuit)
}
*/
