# DS2: completed correspondence with the internal proof

This record supersedes the outstanding DS2 obligations in the historical
partial releases. It does not retroactively change their evidence. The
[source snapshot](DS2-complete-source.json) binds exact internal sections 2–3,
the unchanged DS2/v1 statement, and the new internal proof notes.

1. **Weighted model and normalized gradient:** existing DS1 polynomial
   isometry and L² extension are unchanged. `rowCoefficient_spinorIsometry`
   and `quaternionCoefficients_spinorIsometry` expose the normalization.
2. **Probability mass:** `radial_weight_integral`, `integral_ballScale_pow`
   and `weightedBallMeasure_isProbability` implement the canonical radial
   computation using mathlib's Haar integral, ball volume and FTC.
3. **Conjugate Fueter factorization and injectivity:** the preceding
   `weakKernel_distributionLaplacian_zero` proof is retained, including
   actual distribution derivative commutation and Euler injectivity.
4. **Weyl:** the preceding `weylRegularityOnBall` proves the invoked general
   lemma by the fully recorded regularized-potential/smoothing construction.
5. **Local L² convergence and closedness:** `weakKernel_isClosed_by_localL2`
   implements the compact density lower bound and passage of test equations
   to the limit. `regularKernel_complete_by_localL2` explicitly uses this
   proof. Row completeness transfers through the actual isometry.
6. **Independent row equation:** `rowWeakTest_eq_distribution` and
   `mem_weakRowKernel_iff_distribution` identify the original coefficientwise
   weak equation, with local integrability proved. Together with the prior
   smooth comparison, no regularity condition is defined to be the image
   merely to make the model identification tautological.
7. **Interior harmonic estimates:** `harmonicPartials_test_formula` expands
   the stated estimate using the proved local harmonic smoothing identity
   and repeated integration by parts. `regularPartials_bound` provides each
   finite-order interior L² bound; `regularPartials_integral` proves the
   differentiation/averaging consequence for Bochner-integrable families.
8. **Group law:** existing direct denominator-cocycle proofs and their
   actual L² implementation are unchanged. No lifted substitute is used.
9. **Lift/Schmid covariance:** the existing SC3 proof, smooth/weak comparison
   and `weightedL2Action_mem_weakKernel` implement the canonical route.
   The nonflat connection is retained.
10. **Jacobian/fibre/weight cancellation:** the actual norm-preserving
    ambient L² action uses the already proved change of variables and
    quasi-invariance; no formal integral identity is substituted for integrability.
11. **Strong continuity:** now matches the specified compact-support route.
    `dense_compactContinuousBallClasses` uses compact support in the open B.
    `continuousAt_one_weightedL2Action_compact` combines the change-of-variables
    norm identity with dominated convergence on a fixed compact support.
    Unitarity transfers continuity and supplies the uniform Lipschitz bound
    for dense-class extension. The regular kernel inherits it via
    `stronglyContinuous_regularRepresentation_by_compact`. The previous
    alternative continuity theorems are excluded by the proof-dependency check.
12. **C3/C7 intertwining and transfer:** the polynomial chain rule is
    unchanged; `regularRowRepresentation_ae` identifies the transferred
    action with C3, including inverse, transpose and multiplication sides.
    `regularRow_intertwining` gives the Hilbert-space intertwiner.
13. **Nonzeroness:** the previous constant-vector embedding remains the
    proof; row nonzeroness transfers through the normalized isometry.

`DS2_v1` assembles these conclusions. The extended justifications fill out
brief canonical steps without rewriting the canonical mathematics or wiki.
No unresolved DS2 proof-route alternative remains in this delivery. The
all-order averaging statement has its explicit Bochner-integrability
hypothesis; DS3 compact averaging and irreducibility and DS4 Haar/Schur and
coefficient realization are separate, still uninstantiated claims.

This is an author correspondence check, not independent review or a visitor
approval mechanism. An axiom audit, statement comparison and proof-route
check establish different parts of the evidence and are retained separately.
