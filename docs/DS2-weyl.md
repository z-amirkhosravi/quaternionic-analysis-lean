# DS2: proved Weyl regularity and regular Hilbert action

This continuation proves the formerly missing Weyl regularity premise. It
also proves classical/weak equivalence, regular-kernel invariance, the actual
strongly continuous unitary action on that kernel, bounded point evaluation,
and identification with an independently specified smooth compatible-row space.
It does **not** certify the entire DS2 written proof or instantiate DS3–DS4.

The [exact canonical proof snapshot](DS2-proof-source.json) is unchanged.
Read the [step correspondence](DS2-weyl-proof-correspondence.md), the
[full internal mathematical notes](DS2-weyl-proof-notes.md), and the
[remaining dependencies](DS2-weyl-dependencies.json) alongside the code.

All declarations below are in `MathResearch.Spinor`.

- `Analysis/RadialLaplacian.lean`, `WeylProfile.lean`, `WeylKernel.lean`:
  the explicit regularized Newton potential, its actual Laplacian and the
  normalized compactly supported signed kernels. Their nonzero mass is proved.
- `Analysis/WeylTests.lean`: local scale independence by testing the weak
  Laplace equation against the compactly supported difference of potentials.
- `Analysis/WeylApproximation.lean`, `WeylRepresentative.lean`:
  almost-everywhere recovery using mathlib Lebesgue differentiation; local
  smoothness by fixed-radius convolution after cutoff; countable local-to-global
  agreement. The selected variable radius itself is not differentiated.
- `Analysis/SmoothDistribution.lean`: actual integration by parts, the
  distribution/classical Laplace comparison and pointwise harmonicity.
- `Spinor/WeylRegularity.lean`: `smooth_harmonic_representative` for complete
  real normed codomains, `weylRegularityOnBall` discharging the prior exact
  proposition, and unconditional `weakKernel_smoothRepresentative`.
- `Spinor/ClassicalWeak.lean`: `mem_weakKernel_iff_classicalFueter` and
  `weakKernel_classicalRepresentative`, using the existing coefficient map.
- `Spinor/RegularAction.lean`: `weightedL2Action_mem_weakKernel`,
  `regularRepresentation`, and `stronglyContinuous_regularRepresentation`.
  Invariance uses the existing SC3 lift/Schmid proof, as the notes require.
- `Spinor/RegularEvaluation.lean`: the bounded complex-linear evaluation
  map, its equality to every continuous representative, and its L² bound.
- `Spinor/ClassicalRow.lean`: `HasClassicalRowRepresentative` is defined
  using the actual compatible fibre and classical Fueter operator, before
  `mem_weakRowKernel_iff_classical` proves equivalence to the old weak model.

Paths above are relative to `MathResearch/`. The exact signatures and small
definition/convention comparisons are in
[`DS2-weyl-statement-check.lean`](DS2-weyl-statement-check.lean).
The raw `#print` output is retained in the statement-check evidence.

The ambient strong-continuity proof still uses the previously documented
bounded-continuous approximation alternative. That difference is not closed
by restriction to the regular kernel. Higher derivative/averaging estimates,
the complete C3 row-action assembly and normalized-measure bookkeeping also
remain. New Weyl results have no unproved regularity parameter or external
axiom. The general analytic foundations come from mathlib, not a postulated
PDE theorem.

Replay with the pinned Lean 4.35.0/mathlib environment:

```sh
python3 scripts/verify.py --clean-local
bash scripts/lake.sh env lean -DwarningAsError=true docs/DS2-weyl-statement-check.lean
```

Earlier source modules, dependency pins and checking scripts are preserved.
New evidence is claim-specific; it does not retrospectively certify all older
written arguments. No wiki content or exports are changed.
