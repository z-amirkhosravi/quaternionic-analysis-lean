# Quaternionic analysis in Lean

A Lean 4 library for Fueter regularity and quaternionic analysis, built on mathlib.
The initial library proves both left and right regularity of the Cauchy–Fueter
kernel and every real coordinate partial derivative (F1, version 2).

The library uses mathlib's real quaternions, Euclidean norm, real Fréchet
calculus and smoothness. Its existing `MathResearch.Fueter` namespace is retained
for compatibility with published theorem and definition links.

## Build and check

Lean and mathlib are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`. With the specified Lean toolchain installed:

```sh
lake exe cache get
lake build
```

On Linux x86_64 / WSL the optional `bash scripts/setup.sh` installs the pinned
runtime and cache. `python3 scripts/verify.py --clean-local` recompiles every
local module, audits all declarations for extra axioms and unfinished proofs,
and saves a fingerprinted checking record in `runs/`.

This development is AI-assisted. Proof checking applies to the precise Lean
statements and their definitions. It does not itself establish that an informal
statement was faithfully translated. Accepted verification records permit only
Lean's standard `propext`, `Classical.choice` and `Quot.sound` axioms.
