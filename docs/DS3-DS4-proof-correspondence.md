# DS3–DS4: the written argument with named background inputs

This development follows R060, `corrected-realization.md`, §§4–5. Its source
snapshot is `DS3-DS4-proof-source.json`. The canonical text and wiki are unchanged.
This is author proof-correspondence inspection, not independent review.

**Status: conditional research proofs, not complete verification of DS3 or DS4.**
The concrete Hilbert models, representations, compact Haar measures, evaluation,
matrix coefficients and L² maps are instantiated. The unresolved inputs are
precise standard theorem statements, not the conclusions being proved.

## The background boundary

`Analysis/HarmonicMeanValue.lean` states two unproved propositions:

- `SphericalMeanValueOnBall`: for a smooth harmonic Banach-valued function F on
  the real quaternion ball, the unit-quaternion Haar average of F(a⁻¹q) is F(0).
- `RadialMeanValueOnBall`: the μ_n integral of an integrable smooth harmonic F
  is F(0), for n≥2 and the established probability weight μ_n.

The second is the standard polar-integration corollary of the first. That
implication is **not** formalized here; DS4 has its own explicit radial-mean
hypothesis. This must not be reported as a discharged dependency.

`Analysis/QuotientHaarIntegration.lean` states the unproved proposition
`QuotientHaarIntegration μG`: μG is a Haar measure and, for every nonnegative
continuous φ on G,

    ∫G φ(g) dμG = ∫B s(q)⁻⁴ ∫K φ(σ(q)k) dk dv(q),

with equivalence of integrability on the two sides. Existence of such a
normalized μG is not proved here. The outside-ball value of `ballCompactPoint`
is arbitrary and never integrated. K uses Haar probability on both factors.

These are explicit parameters, not Lean axioms or implicit instances. Passing
an axiom audit does not remove them. No unconditional mean-value or quotient
integration claim is made.

The following two standard inputs are proved independently:

- `Spinor/CompactIrreducible.lean`: `compactPolynomial_irreducible` for degree
  n=m+1. Genuine compact-circle differentiation, distinct weights, and raising
  and lowering prove irreducibility. The n=0 case is not in this signature.
- `Spinor/CompactSchur.lean`: `compactPolynomial_schur` and
  `compactSchurInput_proved`. The average of rank-one operators commutes with
  the action; a separately stated scalar-commutant lemma and trace give the
  orthogonality constant. This proves the positive-degree quaternionic
  specialization, **not** a general theorem for every compact group.

Research proofs invoke these named results. Their background proofs have their
own modules and should have separate expository statements and verification
labels. The internal exposition inventory lists them and the earlier DS2 inputs.

## DS3 correspondence

1. The exact compact action C10 is `ballRepresentation_compact`; its action on
   constants is `regularAction_constant_compact`.
2. `compactRegularOrbit_integrable` uses DS2's canonical strongly continuous
   action and compactness. Bounded point evaluation commutes with this Bochner
   integral using mathlib's `ContinuousLinearMap.integral_comp_comm`.
3. `regular_compact_average` invokes `SphericalMeanValueOnBall` at C11, giving
   the constant with value f(0). It does not derive a substitute mean-value
   formula inside the research proof.
4. `regular_translate_detects` chooses a point where a nonzero smooth
   representative is nonzero, then uses the actual inverse ball section and
   its nonzero fibre multiplier to obtain nonzero evaluation at the origin.
5. `regular_constant_orbit_spans` invokes `compactPolynomial_irreducible` for
   the constants. The elementary invariant-span argument is packaged in
   `equivariant_irreducible_range_le_span` without inserting the background
   irreducibility proof into it.
6. `DS3_irreducible_of_compactAveraging` is the written closed-invariant-subspace
   and orthogonal-complement argument from the earlier development. The concrete
   four inputs are supplied by `regular_compactAveragingInputs`.
7. `DS3_v1_of_meanValue` proves polynomial-model irreducibility and density of
   constant translates. The row statements transport these conclusions using
   the existing normalized isometry and exact intertwining.

The abstract compact-averaging criterion is an abstraction of the written
research argument; it does not replace that argument with a classification
result. Its separate exposition is optional background reuse, not an additional
unverified input.

## DS4 correspondence

1. `regular_inner_constant` invokes the radial mean-value theorem to identify
   pairing with c_v with pairing of f(0) with v. Mathlib's inner product is
   linear in the second slot; `regularCoefficient` reverses the written
   linear-first slots accordingly.
2. `regularCoefficient_eq_lift` is the exact C12 identification. It uses the
   actual regular representation at g⁻¹ and the full lift, for any smooth
   representative of the Hilbert vector. `regularCoefficient_intertwines`
   gives W(π(a)f)(g)=W(f)(a⁻¹g).
3. `regularCoefficient_quotientAverage` uses the section/compact-equivariance
   formula and invokes the separately proved Schur theorem. The power
   cancellation `lift_weight_cancellation` is the written calculation
   s⁻⁴·s^(n+2)=s^(n−2). The resulting factor is
   a_v=‖v‖²/((n+1)C_n).
4. `regularCoefficient_memLp` uses the quotient theorem's integrability clause
   and the original weighted L² hypothesis to establish genuine membership in
   L²(G). This guards against the totalized Bochner integral returning zero for
   a nonintegrable function. It is an integrability justification of the
   written norm calculation, not a separate argument for square-integrability.
5. `regularCoefficient_integral`, `regularCoefficientMap_ae` and
   `regularCoefficientMap_norm` give C13 for the actual L² coefficient map.
6. Mathlib's measure-preserving pullback constructs `leftL2Representation`.
   `regularCoefficientMap_intertwines` proves exact L² intertwining.
7. The positive norm constant gives `regularCoefficientIsometry`; completeness
   gives closed image. `DS4_v1_of_background` supplies the coefficient formula,
   exact norm, injectivity, closed image, intertwining and invariant range,
   with Schur discharged by `compactSchurInput_proved`.
8. `regularRowCoefficientIsometry` transports the normalized embedding through
   the existing row isometry, with intertwining and closed image. Together
   with conditional DS3, these are the claimed discrete-series realizations.

## Earlier work and scope

The earlier 86 mathematical modules and their proofs are preserved. In the
DS2 route inspected here, the research applications already call named Weyl,
interior-estimate and density theorems. Their detailed proofs lie in supporting
modules. A separate background inventory and dependency-boundary audit now
make these available for exposition. No retrospective statement is made that
all earlier targets' written proofs have been audited under the strengthened
correspondence requirement.

The new research proofs contain the written averaging and coefficient
arguments, with routine algebra, representative comparisons and integrability
justifications factored into named lemmas. They introduce no alternative
classification or analytic route. No wiki edit, visitor approval control or
publication is part of this delivery.
