# DS2/v1: the regular Hilbert models and group actions

`MathResearch.Spinor.DS2_v1` assembles DS2 for every n≥2, written as n=m+1
with m≥1. Both models are nonzero complete complex Hilbert spaces. Their
distributional kernels have smooth harmonic representatives. The concrete
C7 and C3 actions are strongly continuous unitary group representations,
intertwined by the normalized gradient. The unchanged weighted measure is
proved to have probability mass one.

The [full declaration](../MathResearch/Spinor/DiscreteSeriesModel.lean) includes
the independent row PDE comparison and actual almost-everywhere action
formulas. The representation definitions have codomain the groups of complex
linear isometry equivalences; unitarity and group laws are part of those types.
The [statement checks](DS2-complete-statement-check.lean) print the declaration
and relevant definitions and check the minimum degree, norms, transpose/right
scalar convention, measure and all-order derivative convention.

Read the [canonical source snapshot](DS2-complete-source.json),
[step correspondence](DS2-complete-proof-correspondence.md), and
[full internal proof notes](DS2-completion-proof-notes.md). The latter expand
the compact-support, interior-estimate, row-distribution and radial-integral
arguments. The prior Weyl construction and SC3 covariance proofs are reused.
There are no undischarged mathematical premises in DS2. DS3 and DS4 retain
their separate inputs in the [dependency record](DS2-complete-dependencies.json).

The eight new modules are:

- `Spinor/CompactDensity.lean`: continuous functions with compact support
  strictly inside B are dense in the actual weighted L² space.
- `Spinor/CompactContinuity.lean`: change-of-variables norm identity,
  compactly dominated matrix coefficients, then density and unitarity.
- `Analysis/HarmonicPartials.lean`: all real directional derivatives remain
  weakly harmonic; repeated integration by parts gives their interior kernel formula.
- `Spinor/InteriorEvaluation.lean`: bounded evaluation of every such derivative
  and commutation with Bochner averaging of integrable Hilbert-space families.
- `Spinor/ProbabilityMeasure.lean`: the exact canonical radial computation
  establishing μ(B)=1 for C_n=n(n−1)/π².
- `Spinor/RegularRowAction.lean`: the row unitary group homomorphism, its
  strong continuity, normalized intertwining and exact C3 formula.
- `Spinor/RowWeakEquation.lean`: local integrability and the actual ordinary
  distributional equation of each coefficient of A−jB, compared with the model.
- `Spinor/DiscreteSeriesModel.lean`: explicit canonical local-L² completeness,
  smooth harmonic representatives and the assembled DS2 theorem.

Paths above are relative to `MathResearch/`. Earlier mathematical modules,
dependency pins and checker scripts remain unchanged.

The historical bounded-continuous continuity argument is preserved but is
not used by the new theorem. The [proof-route check](DS2-proof-route-check.lean)
traverses actual project proof dependencies, requires the compact-support and
change-of-variables steps, and rejects dependence on the four old continuity
theorems. It does not replace the mathematical correspondence record.

Replay with the pinned Lean/mathlib environment:

```sh
python3 scripts/verify.py --clean-local
bash scripts/lake.sh env lean -DwarningAsError=true docs/DS2-complete-statement-check.lean
bash scripts/lake.sh env lean -DwarningAsError=true docs/DS2-proof-route-check.lean
```

This is author formal verification and correspondence inspection, not
independent mathematical review. It does not certify irreducibility,
square-integrability of group coefficients, the Hardy endpoint n=1, or the
whole article. No canonical research text, wiki page or export is edited.
