# DS2 continuation: correspondence with the internal proof

The exact canonical section remains in [DS2-proof-source.json](DS2-proof-source.json).
Its section SHA-256 is
`9a0cd31e6e15ad7a75fd7347059e72f269c0f03d415225452005fa0056f2ac7d`.
This record extends the prior audit; it does not alter its historical scope.
The [new internal notes](DS2-weyl-proof-notes.md) give the full mathematics.

1. **Conjugate Fueter factorization and T_n injectivity:** unchanged from
   the previous release, through `weakKernel_distributionLaplacian_zero`.
2. **Weyl's lemma:** now proved. `smooth_harmonic_representative` constructs
   a smooth harmonic representative of the actual ordinary distribution.
   The regularized-potential/kernel argument is a full expansion of the
   external theorem invoked by the notes; the notes do not specify another
   proof of that lemma. `weylRegularityOnBall` discharges the old exact premise.
3. **Classical/weak model:** now proved by integration by parts and
   distribution injectivity, in `mem_weakKernel_iff_classicalFueter`.
   The old kernel is not replaced by a new PDE definition.
4. **Local L² limit and completeness:** prior canonical local-limit proof is
   preserved. `mem_weakRowKernel_iff_classical` now identifies the row image
   with an independently stated smooth compatible-fibre/Fueter condition.
   Existing Hilbert completeness and nonzeroness apply under that comparison.
5. **Interior estimate for point evaluation:** now proved by the local
   harmonic smoothing formula and mathlib L² Hölder pairing, including
   division by the positive compactly supported weight.
   `regularEvaluation_eq_representative` identifies the bounded map with
   actual evaluation. This expands the evaluation estimate cited in the
   notes; higher differentiation/averaging consequences remain open.
6. **Cocycle group law and Jacobian norm cancellation:** the previous
   direct proofs and actual ambient L² representation are unchanged.
7. **Lift/Schmid covariance on the regular kernel:** now implemented by
   `weightedL2Action_mem_weakKernel`, using the smooth representative,
   existing SC3 covariance and the classical/weak comparison. This matches
   the specified route, with no flat-connection substitution.
8. **Restricted action:** `regularRepresentation` is an actual unitary
   group representation; its strong continuity is inherited by restriction.
   **The ambient approximation argument remains an alternative:** bounded
   continuous density plus finite-mass dominated convergence, where the
   canonical proof specifies compact support. The earlier internal alternative
   notes remain authoritative for that difference. This is not marked resolved.
9. **Normalized row intertwining:** the existing pointwise C3/C7 and L²
   isometry results are preserved, and the classical row model is now
   identified. The complete row-action bundle with its actual C3 formula,
   normalized-measure bookkeeping and consolidated DS2 statement remain
   to be assembled; none is silently inferred to be a new checked declaration.

There is no new unproved external theorem in this delivery. DS3/DS4 inputs
remain as recorded previously. The original DS2 proof is still incomplete
as a formal verification target. Alternatives are recorded internally, not
edited into the wiki. This is an author correspondence check, not independent
review or a human approval gate.
