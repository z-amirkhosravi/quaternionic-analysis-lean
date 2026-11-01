# Separately identifiable standard results

These results support research proofs; they are not new research claims.
Exact signatures, hypotheses, definitions and sources control their formal
scope. Evidence is indexed separately in
`../evidence/standard-theorems-2026-10-31.json`.
The parent notebook's exposition inventory contains the article handoff detail.

1. **Weyl's lemma on the quaternionic unit ball.**
   `smooth_harmonic_representative`, `weylRegularityOnBall` in
   [WeylRegularity.lean](../MathResearch/Spinor/WeylRegularity.lean), with
   `Analysis/Weyl*.lean`. Proved in the earlier DS2 release. The first theorem
   allows any complete real normed target; the exact DS2 interface specializes
   to finite-dimensional targets. No general-domain verification is claimed.
2. **Interior harmonic derivative estimates and Bochner averaging.**
   `harmonicPartials_test_formula`, `regularPartials_bound`,
   `regularPartials_integral` in `Analysis/HarmonicPartials.lean` and
   `Spinor/InteriorEvaluation.lean`. Proved for all finite real-direction lists
   in the weighted ball model, with Hilbert-space Bochner integrability for
   averaging. The continuous-linear-map integral theorem comes from mathlib.
3. **Interior compact-support density.**
   `dense_compactContinuousBallClasses` in
   [CompactDensity.lean](../MathResearch/Spinor/CompactDensity.lean). Proved for
   the weighted quaternionic ball by an attributed adaptation of mathlib's
   Urysohn/simple-function proof. The continuity extension uses mathlib.
4. **Spherical and radial harmonic mean values.**
   `SphericalMeanValueOnBall`, `RadialMeanValueOnBall` in
   [HarmonicMeanValue.lean](../MathResearch/Analysis/HarmonicMeanValue.lean).
   **Unverified hypotheses.** The radial corollary is also not yet derived
   from the spherical assertion. DS3/DS4 retain the corresponding parameters.
5. **Irreducibility of binary forms under unit quaternions.**
   `compactPolynomial_irreducible` in
   [CompactIrreducible.lean](../MathResearch/Spinor/CompactIrreducible.lean).
   Proved for n=m+1, by genuine circle derivatives, distinct H-weights and
   raising/lowering. An article may state n=0 separately but cannot include it
   in this declaration's formal-verification scope.
6. **Schur orthogonality for this compact representation.**
   `compactPolynomial_commutant_scalar`, `compactPolynomial_schur` and
   `compactSchurInput_proved` in
   [CompactSchur.lean](../MathResearch/Spinor/CompactSchur.lean). Proved for
   positive degree, by averaging rank-one operators and computing their trace.
   A theorem for every compact group has not been formalized here.
7. **Quotient Haar integration in ball coordinates.**
   `QuotientHaarIntegration μG` in
   [QuotientHaarIntegration.lean](../MathResearch/Analysis/QuotientHaarIntegration.lean).
   **Unverified hypothesis**, including Haar status, the normalized formula
   for nonnegative continuous functions and integrability equivalence.
   Existence of such a normalized μG is not claimed.
8. **Compact-averaging Hilbert irreducibility criterion.**
   `DS3_irreducible_of_compactAveraging`, `DS3_dense_translateSpan` in
   [CompactAveraging.lean](../MathResearch/Spinor/CompactAveraging.lean).
   Already proved as an abstract version of the written research argument,
   with four explicit inputs. New elementary invariant-span and transport
   proofs are separately in `Analysis/UnitaryIrreducible.lean`.
9. **Quaternionic surjection onto SO(4), kernel {(1,1),(−1,−1)}.**
   `quaternionSpinCover_surjective`, `quaternionRotation_kernel` (namespace
   `MathResearch.Fueter`) in
   [QuaternionRotations.lean](../MathResearch/Fueter/QuaternionRotations.lean).
   Already proved and invoked by EI7. Mathlib supplies Cartan–Dieudonné.
   The topological covering-space claim is not part of these signatures.
10. **Unitarity of the binomially weighted polynomial action.**
    `quaternionAction_norm`, `unitQuaternionAction_norm` in
    [PolynomialUnitary.lean](../MathResearch/Spinor/PolynomialUnitary.lean).
    Already proved for all degrees. It can share an exposition with entry 5.

The Gamma identity and integration interchanges used in TH1 call mathlib;
they are not local reproofs of Gamma or Fubini. Routine algebra and short
measure-preserving pullback wrappers do not require individual articles.

The generality of an expository article may exceed the proved specialization,
but its verification labels must remain attached to exact Lean statements.
Literature attribution and article production belong to the Expositor; this
list does not commission publication or certify historical proof provenance.
