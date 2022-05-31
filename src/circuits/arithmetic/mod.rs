use crate::bool_circuit::*;
use crate::bristol_converter::*;
use crate::circuits::{build_circuit_from_bristol, BuildCircuitError};
use crate::gates::*;
use std::io::BufReader;

mod int;
pub use int::*;

build_circuit_from_bristol!(build_adder64, "adder64.txt");
build_circuit_from_bristol!(build_sub64, "sub64.txt");
build_circuit_from_bristol!(build_neg64, "neg64.txt");
build_circuit_from_bristol!(build_mult2_64, "mult2_64.txt");
build_circuit_from_bristol!(build_divide_signed_64, "divide64.txt");
build_circuit_from_bristol!(build_divide_unsigned_64, "udivide64.txt");
