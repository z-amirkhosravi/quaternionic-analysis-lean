# DS3–DS4: completed concrete realizations

The mean-value and quotient-Haar dependencies are now separately proved. The
new assembly `MathResearch/Spinor/DiscreteSeriesVerified.lean` applies them to
the existing research proofs, which are preserved byte for byte.

All names below have namespace `MathResearch.Spinor`.

- `sphericalMeanValueOnBall_proved`: smooth harmonic functions from the real
  quaternion ball to any complete real normed space have their central value
  as every spherical Haar mean.
- `radialMeanValueOnBall_proved`: an integrable such function has its central
  value as its weighted probability mean for every n≥2.
- `quotientHaarIntegration_proved`: the concrete `normalizedGroupHaar` is Haar;
  nonnegative continuous functions obey the s⁻⁴ dq dk quotient formula, with
  equivalence of integrability. K has Haar probability.
- `DS3_v1`, `DS3_row_v1`: irreducibility and density of constant translates in
  the actual polynomial and compatible-row Hilbert models.
- `DS4_v1`: the actual L² coefficient map, its coefficient formula and exact
  norm, injectivity, closed image, left-translation intertwining and invariant
  range. `DS4_polynomialEmbedding` and `DS4_rowEmbedding` are the normalized
  linear isometries; `DS4_row_v1` gives the row intertwining and closed image.
- `DS4_coefficient_formula`: L² membership and the exact C13 integral formula,
  including the zero coefficient vector.

Research degrees are n=m+1 with m≥1. No external mathematical premise remains
in these research declarations. Their axiom dependencies are checked separately
from the hypotheses and correspondence. This does not include the Hardy
endpoint n=1 or later research claims. The quotient theorem is specialized to
Sp(1,1), not the general quotient-Haar theorem for all groups.

Read the [exact canonical proof snapshot](DS3-DS4-proof-source.json) and
[complete internal background proofs and research correspondence](mean-value-quotient-haar-proofs.md).
The old [conditional correspondence](DS3-DS4-proof-correspondence.md) remains
the step map for the unchanged research argument; its open-input descriptions
are historical and are discharged here. Weighted mean values use rotation
invariance and Fubini, with the earlier polar proof of probability normalization;
that background proof choice is explicitly recorded in the new notes.

The [statement check](DS3-DS4-verified-statement-check.lean) prints definitions,
interfaces, hypotheses and final statements, and instantiates results without
mean-value or Haar parameters. The [proof-route check](DS3-DS4-verified-proof-route-check.lean)
requires actual dependencies on the separate background proofs and on the
canonical research steps, excluding the superseded DS2 continuity alternative.
This is author correspondence inspection, not independent review.

Replay:

```sh
python3 scripts/verify.py --clean-local --verbose-build
bash scripts/lake.sh env lean -DwarningAsError=true docs/DS3-DS4-verified-statement-check.lean
bash scripts/lake.sh env lean -DwarningAsError=true docs/DS3-DS4-verified-proof-route-check.lean
```

Fixed records are `evidence/DS3-DS4-verified-2026-10-31.json`,
`DS3-DS4-verified-statement-check-2026-10-31.json`,
`DS3-DS4-verified-proof-route-2026-10-31.json`,
`DS3-DS4-verified-preservation-2026-10-31.json`, and
`DS3-DS4-verified-background-2026-10-31.json`.
The clean build recompiles this library and reuses the pinned upstream mathlib
release artifacts. All prior mathematical modules and pinned configuration and
checking tools remain unchanged; the cumulative root import is extended.

No canonical research text, wiki content or publication state is changed by
this delivery. Integration and separate background exposition await the
researcher's instruction to Coordinator.
