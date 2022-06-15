pub use hex::FromHexError;
use hex::{decode, encode};
use num_bigint::BigInt;
use num_traits::Zero;

pub fn bits2bytes_le(bits: &[bool]) -> Vec<u8> {
    bits.chunks(8)
        .map(|bits| {
            let mut byte: u8 = 0;
            for i in 0..8 {
                byte += (bits[i] as u8) << i;
            }
            byte
        })
        .collect::<Vec<u8>>()
}

pub fn bytes2bits_le(bytes: &[u8]) -> Vec<bool> {
    bytes
        .into_iter()
        .map(|byte| (0..8).map(|i| (*byte >> i) & 1 == 1).collect::<Vec<bool>>())
        .flatten()
        .collect::<Vec<bool>>()
}

pub fn bits2bytes_be(bits: &[bool]) -> Vec<u8> {
    bits.chunks(8)
        .map(|bits| {
            let mut byte: u8 = 0;
            for i in 0..8 {
                byte += (bits[i] as u8) << (7 - i);
            }
            byte
        })
        .collect::<Vec<u8>>()
}

pub fn bytes2bits_be(bytes: &[u8]) -> Vec<bool> {
    bytes
        .into_iter()
        .map(|byte| {
            (0..8)
                .map(|i| (*byte >> (7 - i)) & 1 == 1)
                .collect::<Vec<bool>>()
        })
        .flatten()
        .collect::<Vec<bool>>()
}

pub fn bytes2hex(bytes: &[u8]) -> String {
    encode(bytes)
}

pub fn hex2bytes(hex: &str) -> Result<Vec<u8>, FromHexError> {
    decode(hex)
}

pub fn ext_gcd(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    let zero = BigInt::zero();
    if b == &zero {
        let one = BigInt::from(1i32);
        return (one, zero, a.clone());
    }
    let q = a / b;
    let r = a % b;
    let (s, t, d) = ext_gcd(b, &r);
    let new_y = (&s) - (&q) * (&t);
    return (t, new_y, d);
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::Rng;

    #[test]
    fn le_convert_test() {
        let mut rng = rand::thread_rng();
        let random: [u8; 4] = [rng.gen(), rng.gen(), rng.gen(), rng.gen()];
        let bits = bytes2bits_le(&random);
        assert_eq!(bits.len(), 32);
        let bytes = bits2bytes_le(&bits);
        assert_eq!(random.to_vec(), bytes);
    }

    #[test]
    fn be_convert_test() {
        let mut rng = rand::thread_rng();
        let random: [u8; 4] = [rng.gen(), rng.gen(), rng.gen(), rng.gen()];
        let bits = bytes2bits_be(&random);
        assert_eq!(bits.len(), 32);
        let bytes = bits2bytes_be(&bits);
        assert_eq!(random.to_vec(), bytes);
    }

    #[test]
    fn hex_test() {
        let mut rng = rand::thread_rng();
        let random: [u8; 4] = [rng.gen(), rng.gen(), rng.gen(), rng.gen()];
        let hex = bytes2hex(&random);
        let bytes = hex2bytes(&hex).unwrap();
        assert_eq!(random.to_vec(), bytes);
    }

    #[test]
    fn ext_gcd_test() {
        let a = BigInt::from(111i32);
        let b = BigInt::from(30i32);
        let (x, y, d) = ext_gcd(&a, &b);
        assert_eq!(a * x + b * y, d);
    }
}
