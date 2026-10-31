# Quaternionic analysis in Lean

A Lean 4 library for Fueter regularity and quaternionic analysis, built on mathlib.

- **F1, version 2:** both left and right regularity of the Cauchy–Fueter kernel
  and every real coordinate partial derivative.
  [Proof](MathResearch/Fueter/Kernel.lean).
- **F2, version 1:** parity, homogeneity and bounds for all real multi-index
  derivatives, including the explicit first spatial derivatives.
  [Statement and correspondence](docs/F2.md) ·
  [Proof](MathResearch/Fueter/KernelEstimates.lean).

- **N2 and N3, version 1:** absolute and local uniform convergence of higher
  lattice sums, periodicity for every lattice period, and even-order parity
  cancellation of their Eisenstein coefficients.
  [Statements and correspondence](docs/N2-N3.md) ·
  [Proof](MathResearch/Fueter/LatticeSums.lean).

- **E1 and E2, version 2:** absolute and compact-uniform convergence of the
  regularized first-derivative elliptic series; termwise differentiation to
  every real order; both Fueter regularities; smooth regular remainders at
  all lattice poles; evenness and lattice periodicity.
  [Statements and correspondence](docs/E1-E2.md) ·
  [E1 proof](MathResearch/Fueter/Elliptic.lean) ·
  [E2 proof](MathResearch/Fueter/EllipticPeriodicity.lean).

- **N1, version 2:** every positive-order spatial derivative at zero of the
  smooth elliptic remainder equals the corresponding Eisenstein coefficient,
  independently of the chosen smooth extension.
  [Statement and correspondence](docs/N1.md) ·
  [Proof](MathResearch/Fueter/EllipticCoefficients.lean).

- **E3, version 2:** absolute and locally uniform convergence of the zeta Taylor
  brackets and all termwise real derivatives; oddness; both Fueter regularities;
  spatial derivatives equal to the elliptic functions; and the unique additive
  quasiperiod map for every lattice period.
  [Statement and correspondence](docs/E3.md) ·
  [Proof](MathResearch/Fueter/ZetaQuasiperiods.lean).

- **E4, E5 and E6, version 1:** zeta values at nonlattice half-periods;
  vanishing of the entire real differential of the elliptic functions there;
  and real dilation laws for elliptic functions, zeta and quasiperiods.
  [Statements and correspondence](docs/E4-E6.md) ·
  [Half-period proofs](MathResearch/Fueter/HalfPeriods.lean) ·
  [Dilation proofs](MathResearch/Fueter/EllipticDilation.lean).

- **EI1 and TH1, version 1:** homogeneous harmonic polynomial numerators for
  every spatial kernel derivative, their recurrence in all spatial directions,
  and the absolutely convergent Mellin formula for each real component of
  every odd-order coefficient of order at least three.
  [Statements and correspondence](docs/EI1-TH1.md) ·
  [EI1 proof](MathResearch/Fueter/KernelNumerator.lean) ·
  [TH1 proof](MathResearch/Fueter/HarmonicTheta.lean).

- **EI7, version 1:** invariance of the right quaternion derivative span,
  absolute coefficient functionals, forward rotation covariance, and a genuine
  real representation descending from unit quaternion pairs to SO(4).
  [Statement and correspondence](docs/EI7.md) ·
  [Proof](MathResearch/Fueter/RotationCovariance.lean).

- **DS1, version 1:** the spinor-to-Fueter complex linear isometric
  isomorphism in every positive degree, including its explicit inverse,
  right complex-scalar convention and dimension formula.
  [Statement and correspondence](docs/DS1.md) ·
  [Proof](MathResearch/Spinor/GradientIsometry.lean).

- **SC2, version 1, and the polynomial representation:** the exact matrix and
  quaternion actions, their analytic infinitesimal actions, and both projected
  connection identities for every positive degree and every quaternion.
  [Statements and correspondence](docs/SC2.md) ·
  [Proof](MathResearch/Spinor/ProjectedConnection.lean).

The library uses mathlib's real quaternions, Euclidean norm, real Fréchet calculus
and smoothness. The `MathResearch.Fueter` namespace and original F1 source files
are retained for compatibility with published theorem and definition links.
This repository is the source for new development. Historical F1 wiki exports
remain fixed to the exact sources and checking evidence of their release.

## Build and check

Lean **4.35.0** and mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`. With the specified Lean toolchain installed:

```sh
lake exe cache get
lake build
python3 scripts/verify.py --clean-local
```

To import the library in another Lake project, add this repository as a Git
dependency pinned to a commit, then `import MathResearch`. Individual modules
can be imported separately. No research-notebook checkout is required.

On Linux x86_64 / WSL, `bash scripts/setup.sh` optionally installs the pinned
runtime and mathlib release cache without changing shell profiles. Dependencies
are kept on native Linux storage. Other platforms can use their normal elan
installation. The bootstrap requires Git, curl, Python 3, a C compiler and the
usual shell tools; allow roughly 11 GB for the toolchain and mathlib cache.

The verifier recompiles every local module, including modules not imported by
the root, audits all declarations for extra axioms and unfinished proofs, and
saves a fingerprinted record in `runs/`. Only `propext`, `Classical.choice` and
`Quot.sound` are accepted. Dependency revisions must match the lockfile.
`python3 scripts/test_verification.py` exercises the verifier's rejection paths;
run it without simultaneous source edits or another proof checker.

GitHub Actions runs the pinned bootstrap, verifier controls and a final clean
local build/audit on pushes and pull requests. Upstream compiled mathlib release
artifacts are reused; a clean local build does not rebuild all of mathlib.

This development is AI-assisted. Checking establishes the precise Lean
statements from their definitions and admitted standard axioms. Correspondence
with informal mathematics is explained separately; neither compilation nor
an axiom audit can establish that correspondence by itself.
