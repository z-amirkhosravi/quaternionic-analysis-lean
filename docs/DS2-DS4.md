# DS2–DS4: weak Hilbert spaces and conditional representation arguments

**Status: partial DS2/v1; conditional DS3/v1 and DS4/v1. None of the three
complete wiki statements is claimed verified.** This is one cumulative attempt
at the full analytic/representation milestone, rather than a succession of
new theorem tags for its elementary lemmas. All eighteen previously delivered
targets remain unchanged.

The [accepted source snapshot](DS2-DS4-source.json) fixes the written statements
and conventions at Math Research revision
`8753be59dcf8725a8dd83ce905293b015030ba7c`. The
[compiler statement checks](DS2-DS4-statement-check.lean) display the precise
hypotheses and small definition comparisons. The
[dependency record](DS2-DS4-dependencies.json) separates proved results,
undischarged theorem parameters, and missing local constructions. There is no
visitor approval state or human gate.

## What is proved without external mathematical assumptions

All declarations below are in `MathResearch.Spinor`. The usual parameter n≥2
is sometimes written n=m+1 with m≥1; it includes n=2.

| Part of the argument | Exact declarations | Source |
|---|---|---|
| Every quaternion scales the binomial polynomial norm by its norm to degree n | `quaternionAction_norm`, `unitQuaternionAction_norm` | [PolynomialUnitary](../MathResearch/Spinor/PolynomialUnitary.lean) |
| The actual matrix group, ball action, noncommutative cocycle and C7 group law | `Sp11`, `mobiusDenominator_cocycle`, `mobiusPoint_mul`, `ballRepresentation_mul` | [MobiusLaws](../MathResearch/Spinor/MobiusLaws.lean) |
| The real derivative v↦(a−q'c)vJ⁻¹ and its positive determinant | `hasFDerivAt_mobiusPoint`, `mobiusJacobian` | [MobiusJacobian](../MathResearch/Spinor/MobiusJacobian.lean) |
| The exact weighted square-integral cancellation under C7 | `weighted_density_cancellation`, `weighted_integral_ballAction` | [WeightedMeasure](../MathResearch/Spinor/WeightedMeasure.lean) |
| Closedness/completeness of the specified weak kernel | `weakKernel_isClosed`, `weakKernel_completeSpace` | [WeakKernel](../MathResearch/Spinor/WeakKernel.lean) |
| Its tests really are Lebesgue weak differential tests; constants lie in it and inject | `weakTest_toLp`, `constant_mem_weakKernel`, `constantWeakEmbedding_injective` | [WeakConstants](../MathResearch/Spinor/WeakConstants.lean) |
| Pointwise normalized-gradient isometry on actual weighted L² equivalence classes; both weak models nonzero and complete | `spinorL2Isometry`, `weakSpinorIsometry`, `DS2_weak_models` | [WeakRowSpace](../MathResearch/Spinor/WeakRowSpace.lean) |
| The explicit row action, transpose and right complex factors; normalized C3/C7 intertwining | `fueterCoefficients_action`, `DS2_row_intertwining` | [RowAction](../MathResearch/Spinor/RowAction.lean) |
| The lifted coefficient intertwines with left translation | `liftedCoefficient_intertwines` | [CoefficientEmbedding](../MathResearch/Spinor/CoefficientEmbedding.lean) |

The old SC3 proof continues to supply covariance of the **classical**
differential kernel. It has not been silently promoted to a result about weak
L² equivalence classes.

## Small definition correspondences

* `Sp11` is the subtype of quaternion matrices satisfying the two inverse
  equations for Jg*J from SC1/SC3, now with a proved group structure. `Ball` is
  the actual quaternion unit ball, not an abstract homogeneous space.
* `weightConstant n=(n:ℝ)*((n:ℝ)-1)/π²`. Its subtraction is real subtraction.
  `ballDensity n q=weightConstant n*(1−normSq q)^(n−2)` uses a natural exponent
  and is only used in the discrete-series conclusions for n≥2.
* `weightedBallMeasure` is mathlib's real Euclidean volume restricted to B,
  with density `ENNReal.ofReal (ballDensity n)`. Its positivity on B, finite
  mass, and equivalence of null sets with restricted volume are proved.
  **Its total mass being exactly one is not yet proved.**
* `BallL2 n` is mathlib `Lp (BinaryForm n) 2 (weightedBallMeasure n)`, not a
  space whose norm is assumed to have the desired properties.
* `BallTest` is mathlib's space of all real smooth compactly supported test
  functions with topological support in B. Let A_(μ,j,d) be the complex
  coefficient functional of ι(e_μ)(p_X,p_Y)^t. `weakSymbol` is precisely this
  functional. It quantifies over every j∈Fin 2 and every polynomial exponent
  d∈(Fin 2→₀ℕ), not just a sampled list.
* `weakTestVector` is w⁻¹∑_μ (∂_μφ) A_(μ,j,d)^*1. Its support lies in the
  test function's compact support, so it is continuous and lies in weighted
  L² despite the inverse density. `weakTest` pairs this vector against f using
  mathlib's L² inner product. `weakTest_toLp` proves the exact identity
  
  `weakTest φ j d [f] = ∫_B ∑_μ (∂_μφ) A_(μ,j,d)(f) dv`.
  
  The minus sign in a distributional derivative is immaterial to a zero
  equation. Real tests suffice for the complex coefficient equation by
  real/imaginary decomposition; no complex-valued test is asserted by an
  unproved library coercion. `weakKernel` is the intersection of all these
  continuous linear kernels. Closedness uses mathlib, and nonzeroness uses
  mathlib integration by parts, not a regularity assumption.
* `weakRowKernel` is explicitly the **image** of this kernel under the
  pointwise L² extension of DS1's `spinorIsometry`. This yields a nonzero
  complete compatible-row model and a concrete complex linear isometry.
  It is not defined to be a space of smooth functions, and it does not assert
  a theorem identifying a separately constructed space of row distributions.
* `coefficientActionMatrix m M` has, as column l, the coefficients of
  τ_m(M) applied to the l-th monomial. `rowSubstitution` is the sum
  ∑_l h_l S^t_(l,k), with complex entries embedded in ℍ on the **right**.
  The left factor J⁻¹ and the inverse-group convention are explicit in
  `rowBallRepresentation`. `normalizedFueterRow` is T_n/n.
* Mathlib's complex inner product is linear in the **second** argument.
  `liftedCoefficient n v f g = inner ℂ v (fullLift n f g)` therefore matches
  the wiki's linear-first ⟨F_f(g),v⟩. The further equality to the Hilbert
  matrix coefficient ⟨π(g⁻¹)f,c_v⟩ is still pending.

`weighted_integral_ballAction` is an equality of total Bochner integrals,
proved by mathlib's Jacobian change-of-variables theorem. It remains true
under mathlib's convention for nonintegrable functions. **It does not by itself
prove square-integrability, representative independence, or existence of the
L² action.** This distinction is also retained for the conditional DS4
integral calculation.

## DS3: the complete abstract argument, with four unproved inputs

[CompactAveraging.lean](../MathResearch/Spinor/CompactAveraging.lean) defines
`TopologicallyIrreducible` using **closed** invariant complex subspaces.
It deliberately does not use mathlib's algebraic irreducibility notion.

`DS3_irreducible_of_compactAveraging` takes an actual unitary representation
ρ:G→*(H≃ₗᵢ[ℂ]H) on a complete Hilbert space, a nonzero coefficient space V,
a linear isometric constant embedding c, a continuous evaluation ev₀, and
a probability measure on an averaging parameter space. Its
`CompactAveragingInputs` fields are all visible in the statement check:

1. each compact orbit is Bochner integrable;
2. its average is c(ev₀ f);
3. every nonzero vector has a translate with nonzero origin evaluation;
4. the G-orbit of any nonzero constant spans the whole constant subspace.

For the intended model these require the actual compact action, harmonic
spherical mean identity, evaluation/separation and transitivity, and
irreducibility of τ_n on the second compact factor. They are **not yet
instantiated for `WeakBallSpace`**. Field 4 is the orbit-spanning consequence
needed from finite-dimensional compact irreducibility; it does not assert
irreducibility of H.

The Lean proof establishes that a nonzero closed invariant M contains all
constants, proves invariance of M⊥ from unitarity, and uses completeness and
orthogonal projection to exclude proper M. It proves, separately, that the
translates of every nonzero constant subspace have dense span. The latter
follows by verifying invariance of the span and its topological closure.

## DS4: exact norm calculation and conditional closed embedding

`CompactSchurInput n μK` states the precise finite-dimensional integral

`∫_K |inner ℂ v (τ_n(k_R⁻¹)u)|² dμK = ‖u‖²‖v‖²/(n+1)`.

`CoefficientHaarInput n μG μK v f` states the displayed Haar-coordinate
integral for the square of the **concrete lifted coefficient**, before the
compact integration or radial cancellation. Neither proposition is supplied
as an axiom or a proved instance. No existence or left-invariance theorem
for μG has been proved here; μK and μG are explicit measure parameters.

`DS4_coefficient_integral_of_haar_schur` derives C13's constant from these
inputs using the already proved full-lift section formula and right
K-equivariance. Lean verifies s⁻⁴(s^((n+2)/2))²=s^(n−2), including n=2, and
obtains exactly ‖v‖²/((n+1)C_n).

`DS4_closed_embedding_of_inputs` also takes:

* a complete normed complex space H with a representative function whose
  weighted integral gives its squared norm;
* an actual complex linear map W:H→L²(G) whose values agree almost everywhere
  with the concrete lifted coefficient;
* the Haar-coordinate identity for each representative.

It proves the norm identity, injectivity for v≠0, and closed range. The proof
constructs the explicitly scaled linear isometry a^(-1/2)W and uses
completeness of H. The existence/linearity/integrability of W is a **missing
local bridge**, not a disguised imported theorem. The norm identity is derived
from the integral hypotheses; it is not taken as an external assumption in
this combined theorem.

This does not yet prove the full discrete-series claim. In particular, the
Haar/Schur inputs, actual Hilbert matrix-coefficient interpretation,
left-regular L² intertwining, and the concrete DS3 instantiation remain open.

## Remaining work and external theorem boundary

The next milestone is to close the analytic bridge, not add more algebraic
lemmas. The dependency JSON lists every remaining item and its affected
conclusions. In particular:

* **Weyl regularity:** weak Fueter solutions must first be shown distributionally
  harmonic, then given smooth harmonic representatives. This needs the
  distributional operator factorization and injectivity of T_n, not just a
  citation of Weyl's lemma. Local-to-global representative uniqueness and the
  classical/weak comparison must also be proved.
* **Weighted L² representation:** descend C7 to equivalence classes, establish
  square-integrability and kernel preservation, and prove strong continuity.
  The classical covariance, exact group laws, norm cancellation and null-set
  equivalence are now available. The compact-support approximation argument
  still needs to be implemented for the nonconstant fibre multiplier.
* **Evaluation/mean values and finite-dimensional representation theory:**
  establish bounded evaluation, the constant embedding's normalization,
  harmonic compact averaging, and irreducibility of τ_n; instantiate DS3.
* **Haar coordinates and Schur orthogonality:** supply the exact formulas above,
  with integrability/measurability, then build W and connect its function-level
  intertwining to left translation on L²(G).

Weyl regularity, harmonic mean values, finite-dimensional compact
irreducibility/Schur orthogonality, and Haar disintegration are familiar
mathematical inputs. Their exact formal versions and the local applications
are **not certified by calling them standard**. The provenance in this
attempt is the accepted wiki proof and R060 derivation; no independently
registered external theorem has been imported. Such an import would require
an exact source statement and convention audit. The conditional Lean
parameters already expose what must be supplied.

## mathlib reuse and checking

The pin remains Lean 4.35.0 / mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. This development reuses homogeneous
polynomials and their derivatives, quaternion norms and real Fréchet calculus,
finite-dimensional continuous linear maps/adjoints, Euclidean volume,
Jacobian change of variables, `TestFunction`, `Lp` and Bochner integration,
integration by parts, closed submodules, orthogonal complements/projections,
and linear isometry completeness results.

The scoped API investigation found a continuous Lp domain action for
measure-preserving actions in `MeasureTheory/Function/LpSpace/DomAct/Continuous`;
it does not directly cover the C7 fibre multiplier. General Weyl regularity
and the required compact Schur integral were not located in the inspected
pinned APIs. This is a search finding, not a claim that mathlib can never
contain them.

Replay the complete local build and transitive axiom audit with
`python3 scripts/verify.py --clean-local`; replay exact signatures with
`bash scripts/lake.sh env lean -DwarningAsError=true docs/DS2-DS4-statement-check.lean`.
The retained JSON records give the exact commands, output, versions, hashes,
and audit. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
**A clean axiom audit does not discharge explicit theorem hypotheses.**
The partial/conditional status must accompany any links to these proofs.
