# DateSAT Verification

This repository contains (work-in-progress) machine-checked proofs of formal semantics for DateSAT.

First, [install Verus](https://github.com/verus-lang/verus/blob/main/INSTALL.md).

Then, in this repository, run `/path/to/verus src/main.rs`

To also verify the slow non-linear arithmetic proofs (disabled by default), run:

`/path/to/verus src/main.rs -- --cfg slow_proofs`
