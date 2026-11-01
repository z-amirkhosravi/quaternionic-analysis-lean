# DS3–DS4: conditional concrete realizations

The written compact-averaging and coefficient arguments are now formalized for
the actual polynomial and compatible-row Hilbert models. **DS3 and DS4 remain
conditional**, with precise standard theorem inputs visible in their signatures.

- DS3: `DS3_v1_of_meanValue`, `DS3_row_of_meanValue` and
  `DS3_row_dense_of_meanValue` give irreducibility and dense constant translates,
  assuming `SphericalMeanValueOnBall`.
- DS4: `DS4_v1_of_background` gives the actual L² matrix coefficient map,
  C12/C13, injectivity, closed image, exact left-translation intertwining and
  invariant range, assuming `RadialMeanValueOnBall` and
  `QuotientHaarIntegration μG`. Normalized polynomial and row isometries and
  the row intertwining/closed-image assertions are also constructed.
- `compactPolynomial_irreducible`, `compactPolynomial_schur` and
  `compactSchurInput_proved` are independently proved standard inputs, in
  separate modules. Their scope is the positive-degree quaternionic polynomial
  representation, not all compact groups or an unproved n=0 extension.

All names above except `MathResearch.leftL2Representation` have namespace
`MathResearch.Spinor`. Research degrees are n=m+1 with m≥1, exactly n≥2.

Read the [exact canonical proof snapshot](DS3-DS4-proof-source.json),
[step correspondence and open inputs](DS3-DS4-proof-correspondence.md),
[background inventory](standard-theorems.md), and
[bounded audit of earlier theorem boundaries](background-theorem-boundaries.md).
The statement check prints the assumptions, definitions and theorem signatures.
An axiom audit alone cannot disclose or discharge theorem parameters.

Replay from the repository root:

```sh
python3 scripts/verify.py --clean-local
bash scripts/lake.sh env lean -DwarningAsError=true docs/DS3-DS4-statement-check.lean
bash scripts/lake.sh env lean -DwarningAsError=true docs/DS3-DS4-proof-route-check.lean
```

Fixed run records are in `evidence/DS3-DS4-conditional-2026-10-31.json`,
`DS3-DS4-statement-check-2026-10-31.json`, and
`DS3-DS4-proof-route-2026-10-31.json`. The background results have a separate
claim-specific index in `standard-theorems-2026-10-31.json` referencing that audit.
Preservation evidence compares all previous mathematical modules and the pinned
configuration/checker files with the DS2 release. Earlier releases remain intact.

No canonical research text, wiki content, exports or publication state are
changed. The formalization and correspondence checks are author verification,
not independent review or a visitor approval process.
