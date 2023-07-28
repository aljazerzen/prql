#![cfg(not(target_family = "wasm"))]

/// As well as the examples in the book, we also test the examples in the
/// website & README in this integration test binary.
mod book;
mod readme;
mod website;

use ::prqlc_main::Options;

fn compile(prql: &str) -> Result<String, prqlc_main::ErrorMessages> {
    anstream::ColorChoice::Never.write_global();
    prqlc_main::compile(prql, &Options::default().no_signature())
}
