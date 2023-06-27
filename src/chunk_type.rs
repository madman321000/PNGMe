use crate::{Error, Result};

#[derive(Debug, PartialEq)]
pub struct ChunkType {
    bytes: [u8; 4],
}

impl ChunkType {
    fn bytes(&self) -> [u8; 4] {
        self.bytes
    }
    fn is_valid(&self) -> bool {
        self.is_reserved_bit_valid()
    }
    fn is_critical(&self) -> bool {
        (self.bytes[0] & (1 << 5)) == 0
    }
    fn is_public(&self) -> bool {
        (self.bytes[1] & (1 << 5)) == 0
    }
    fn is_reserved_bit_valid(&self) -> bool {
        (self.bytes[2] & (1 << 5)) == 0
    }
    fn is_safe_to_copy(&self) -> bool {
        !((self.bytes[3] & (1 << 5)) == 0)
    }
    fn byte_in_range(byte: u8) -> bool {
        (65 <= byte && byte <= 90) || (97 <= byte && byte <= 122)
    }
}

#[derive(Debug)]
pub enum ChunkTypeReadingError {
    InvalidByte(u8),

    InvalidLength(usize),
}

impl std::fmt::Display for ChunkTypeReadingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidByte(byte) => write!(f, "Bad Byte Read {}", byte),
            Self::InvalidLength(size) => write!(f, "Bad size {}, expected 4", size)
        }
    }
}

impl std::error::Error for ChunkTypeReadingError {}

impl std::convert::TryFrom<[u8; 4]> for ChunkType {
    type Error = Error;

    fn try_from(bytes: [u8; 4]) -> Result<Self> {
        for byte in bytes.iter() {
            if !Self::byte_in_range(*byte) {
                return Err(Box::new(ChunkTypeReadingError::InvalidByte(*byte)));
            }
        }
        Ok(ChunkType { bytes })
    }

}

impl std::str::FromStr for ChunkType {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        if s.len() != 4 {
            return Err(Box::new(ChunkTypeReadingError::InvalidLength(s.len())));
        }

        let mut vec: [u8; 4] = [0; 4];

        for (index, byte) in s.as_bytes().iter().enumerate() {
            if Self::byte_in_range(*byte) {
                vec[index] = *byte;
            } else {
                return Err(Box::new(ChunkTypeReadingError::InvalidByte(*byte)));
            }
        }
        Ok(ChunkType { bytes:vec })
    }
}

impl std::fmt::Display for ChunkType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for byte in &self.bytes() {
            write!(f, "{}", char::from(*byte))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryFrom;
    use std::str::FromStr;

    #[test]
    pub fn test_chunk_type_from_bytes() {
        let expected = [82, 117, 83, 116];
        let actual = ChunkType::try_from([82, 117, 83, 116]).unwrap();

        assert_eq!(expected, actual.bytes());
    }

    #[test]
    pub fn test_chunk_type_from_str() {
        let expected = ChunkType::try_from([82, 117, 83, 116]).unwrap();
        let actual = ChunkType::from_str("RuSt").unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    pub fn test_chunk_type_is_critical() {
        let chunk = ChunkType::from_str("RuSt").unwrap();
        assert!(chunk.is_critical());
    }

    #[test]
    pub fn test_chunk_type_is_not_critical() {
        let chunk = ChunkType::from_str("ruSt").unwrap();
        assert!(!chunk.is_critical());
    }

    #[test]
    pub fn test_chunk_type_is_public() {
        let chunk = ChunkType::from_str("RUSt").unwrap();
        assert!(chunk.is_public());
    }

    #[test]
    pub fn test_chunk_type_is_not_public() {
        let chunk = ChunkType::from_str("RuSt").unwrap();
        assert!(!chunk.is_public());
    }

    #[test]
    pub fn test_chunk_type_is_reserved_bit_valid() {
        let chunk = ChunkType::from_str("RuSt").unwrap();
        assert!(chunk.is_reserved_bit_valid());
    }

    #[test]
    pub fn test_chunk_type_is_reserved_bit_invalid() {
        let chunk = ChunkType::from_str("Rust").unwrap();
        assert!(!chunk.is_reserved_bit_valid());
    }

    #[test]
    pub fn test_chunk_type_is_safe_to_copy() {
        let chunk = ChunkType::from_str("RuSt").unwrap();
        assert!(chunk.is_safe_to_copy());
    }

    #[test]
    pub fn test_chunk_type_is_unsafe_to_copy() {
        let chunk = ChunkType::from_str("RuST").unwrap();
        assert!(!chunk.is_safe_to_copy());
    }

    #[test]
    pub fn test_valid_chunk_is_valid() {
        let chunk = ChunkType::from_str("RuSt").unwrap();
        assert!(chunk.is_valid());
    }

    #[test]
    pub fn test_invalid_chunk_is_valid() {
        let chunk = ChunkType::from_str("Rust").unwrap();
        assert!(!chunk.is_valid());

        let chunk = ChunkType::from_str("Ru1t");
        assert!(chunk.is_err());
    }

    #[test]
    pub fn test_chunk_type_string() {
        let chunk = ChunkType::from_str("RuSt").unwrap();
        assert_eq!(&chunk.to_string(), "RuSt");
    }

    #[test]
    pub fn test_chunk_type_trait_impls() {
        let chunk_type_1: ChunkType = TryFrom::try_from([82, 117, 83, 116]).unwrap();
        let chunk_type_2: ChunkType = FromStr::from_str("RuSt").unwrap();
        let _chunk_string = format!("{}", chunk_type_1);
        let _are_chunks_equal = chunk_type_1 == chunk_type_2;
    }
}