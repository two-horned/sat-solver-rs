#!/bin/sh
cargo clean
RUSTFLAGS="-C target-cpu=native" cargo rustc --release --lib -- --emit asm
cat examples/sample_3.txt | RUSTFLAGS="-C target-cpu=native" cargo r --profile dev
