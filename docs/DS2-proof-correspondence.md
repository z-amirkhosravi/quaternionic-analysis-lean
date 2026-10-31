# DS2: correspondence with the written argument

This is a working proof audit, not a completed verification of DS2. The
researcher's requirement of 31 October 2026 is to verify the written argument
itself. A different Lean proof of the same conclusion does not satisfy that
requirement. The internal research notes are the mathematical source; the wiki
is their exposition. Resolve substantive differences in Lean first; where a
different argument is necessary, retain it as an alternative in internal notes,
with its justification and differences from the canonical argument. Reconcile
the internal mathematics and bind evidence to the resulting proof revision.
Merely listing a mismatch does not resolve it. Wiki editing is an expositor's
task, not part of this Lean assignment.

[The source record](DS2-proof-source.json) retains the canonical internal proof
in R060's `corrected-realization.md`, section 3, and the exact DS2/v1 statement
and expository proof separately, with separate SHA-256 fingerprints, at Math Research
revision `8753be59dcf8725a8dd83ce905293b015030ba7c`. The earlier release at
`2bd70840d38a5bcf797c0f8be90f1cd2b2391b25` certified only its recorded partial
and conditional Lean results. It did not verify the complete written DS2–DS4
proofs. Historical evidence is preserved with that scope.

## Step correspondence and outstanding obligations

1. **Interpret the weighted weak kernel using ordinary distributions.**
   `weakTest_toLp` identifies the weighted Hilbert test with the ordinary
   Lebesgue integral. `memLp_locallyIntegrableOn_ball` supplies local Lebesgue
   integrability, and `spinorDistribution` uses mathlib's `Distribution.ofFun`.
   `spinorDistribution_injective` proves that this distribution determines the
   weighted L² class. These are expanded justifications of the text's use of
   distributional equations, not a substitute PDE or a new hypothesis.

2. **Apply the conjugate Fueter operator and use injectivity of T_n.**
   `testDirectional_comm` proves commutation of test derivatives by mathlib's
   symmetry of the second Fréchet derivative.
   `weakKernel_distribution_fueter` translates the exact existing weak kernel
   to the quaternion equation. `quaternion_laplacian_contraction` is the
   coefficient cancellation in conjugate-D times D; it retains the symmetry
   assumption. `fueterCoefficient_jointly_injective` uses Euler's homogeneous
   polynomial identity. `weakKernel_distribution_harmonic` combines these
   steps, precisely as in the first paragraph of the written proof. This is
   weak harmonicity, not smoothness.

3. **Apply Weyl's lemma.** Unfinished. `WeylRegularityOnBall` states the exact
   missing general Laplace-regularity input for a finite-dimensional real
   normed space; it is a proposition, not an axiom or a supplied instance.
   `weakKernel_smoothRepresentative_of_weyl` applies this explicit input to
   the proved distributional harmonicity. `continuousRepresentative_unique`
   proves uniqueness on B if such continuous representatives exist. No
   unconditional smooth-representative theorem or classical/weak comparison
   has been established. The absence of an identified mathlib Weyl theorem
   does not license substituting a Fueter-regularity assumption.

4. **Pass from weighted L² convergence to L² convergence on compact subsets.**
   The original Lean release did not implement this sentence. The continuation
   adds the positive compact lower bound on the density, the corresponding
   measure domination, and a continuous restriction to ordinary local L².
   `ballDensity_compact_lower_bound`, `compact_volume_le_weighted`,
   `compactL2Restriction` and `weightedL2_tendsto_locally` now implement the
   sentence. The continuous restriction is mathlib's
   `Lp.LpToLpOfMeasureLeSMul`, using the proved bound on measures.

5. **Pass the equation and the fibre constraint to the limit; obtain completeness.**
   The earlier `weakKernel_isClosed` directly used an intersection of kernels
   of continuous functionals. That is a checked closedness proof, but it did
   not supply the local L² passage in the written argument. Resolve the
   correspondence is repaired for the polynomial weak kernel by
   `weakTest_eq_local`, `weakKernel_closed_under_localL2_limits` and
   `weakKernel_isClosed_by_localL2`. These pass the test equation to the limit
   in ordinary L² on each test's compact support, using step 4. This proof does
   not use the older `weakKernel_isClosed` theorem. Moreover,
   `weakRowKernel` is currently defined as the image under the L² extension
   of DS1, not independently as a space of row distributions. Its equivalence
   to the written row equation, and smoothness, still require proof.

6. **Interior harmonic estimates imply continuous evaluation.** Unfinished.
   Neither closedness nor weak harmonicity proves this step. No bounded
   evaluation, differentiation or averaging assertion is certified merely by
   the earlier Hilbert-space construction.

7. **The denominator cocycle gives the group law.** The earlier
   `mobiusDenominator_cocycle` and `mobiusPoint_mul` supply the algebra. A
   closer audit found that the older `ballRepresentation_mul` used the lifted
   realization, rather than directly applying the cocycle. The continuation
   repairs this difference with `ballAction_mul_by_cocycle` and
   `ballRepresentation_mul_by_cocycle`. The new L² representation actually
   uses the latter proof, together with the null-set/pullback argument.

8. **The polynomial chain rule gives the normalized row intertwining.**
   `DS2_row_intertwining` uses that chain rule, the normalization T_n/n and
   the stated transpose/right-complex convention. The L² and smooth-kernel
   identifications must be supplied before this is the full DS2 intertwiner.

9. **The lifted connection identity gives covariance.** The existing SC3
   development proves the classical lift, connection/weight identity and
   classical covariance through left translation. This matches the written
   route. Applying it to weak equivalence classes requires steps 1–3 and the
   classical/weak comparison; it has not been promoted silently.

10. **The scale, Jacobian and fibre-norm factors cancel.**
    `ballScale_mobius`, `mobiusJacobian`, `ballAction_norm` and
    `weighted_density_cancellation` implement the three displayed formulas.
    `weighted_integral_ballAction` applies mathlib's Jacobian theorem.
    Its total-integral equality alone does not prove integrability or a
    well-defined unitary L² action. The continuation now proves these separately:
    `mobius_map_jacobian` and `mobius_quasiMeasurePreserving_weighted` establish
    the null-set behavior, `ballAction_memLp` applies the integrability form of
    the same Jacobian theorem, and `weightedL2Representation` is the actual
    unitary action on equivalence classes. Kernel invariance remains unfinished.

11. **Strong continuity by compactly supported continuous approximation.**
    The exact canonical route remains unformalized. An alternative ambient
    proof is now supplied by `continuous_weightedL2Action_boundedContinuous`,
    `continuous_weightedL2Representation` and
    `stronglyContinuous_weightedL2Representation`. It uses bounded continuous
    approximation, finite weighted mass, an explicit uniform multiplier bound
    near each group element and dominated convergence, then density and
    unitarity. This mathematical difference is retained in the internal proof
    notes and the standalone continuation guide. It does not retroactively
    verify the canonical compact-support argument. Restriction to the regular
    kernel still requires its invariance.

12. **Constants show nonzeroness.** The earlier
    `constant_mem_weakKernel` and `constantWeakEmbedding_injective` use finite
    weighted mass and integration by parts. These expand the stated constant
    example. Identifying this weak example with the written smooth space
    still requires the model comparison in steps 3 and 5.

No written article has been changed by this continuation. Necessary alternatives
belong in internal proof notes and are submitted with the formal evidence through
the project's Coordinator mailbox. Any subsequent exposition is a separate task.
This audit is the author's correspondence check, not independent review and
not a visitor approval mechanism.
