// Encoder module: CSP to SAT encoding
// Based on Scarab's Encoder, Simplifier, and OrderEncoder

pub mod traits;
pub mod simplifier;
pub mod order_encoder_le;
pub mod order_encoder_ge;
pub mod direct_encoder;
pub mod log_encoder;

pub use traits::{
    SatSolverBackend, Encoder, EncoderState,
    TRUE_LIT, FALSE_LIT,
    floor_div, ceil_div,
};
pub use simplifier::Simplifier;
pub use order_encoder_le::OrderEncoderLe;
pub use order_encoder_ge::OrderEncoderGe;
pub use direct_encoder::DirectEncoder;
pub use log_encoder::LogEncoder;
