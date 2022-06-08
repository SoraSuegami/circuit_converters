pub mod arithmetic;
pub mod cryptography;
pub mod finite_field;
pub mod logic;
use crate::bool_circuit::BoolCircuitError;
use crate::bristol_converter::*;
pub use crate::cryptography::BuildCryptographicCircuitError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum BuildCircuitError {
    #[error(transparent)]
    BoolCircuitError(#[from] BoolCircuitError),
    #[error(transparent)]
    BristolError(#[from] BristolError),
    #[error(transparent)]
    BuildCryptographicCircuitError(#[from] BuildCryptographicCircuitError),
}

macro_rules! build_circuit_from_bristol {
    ($name:ident,$path:literal) => {
        pub fn $name<G: Gate, C: BoolCircuit<G>>() -> Result<C, BuildCircuitError> {
            let mut reader = BristolReader::<G, C>::new();
            let textfile = include_str!($path).to_string();
            let buf_read = BufReader::new(textfile.as_bytes());
            let circuit = reader.read(buf_read)?;
            Ok(circuit)
        }
    };
}
pub(crate) use build_circuit_from_bristol;
