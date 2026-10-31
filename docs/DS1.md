# DS1/v1 — spinor-to-Fueter isometry

This is the first formalized foundation on the Sp(1,1) discrete-series / Hardy
branch. For every integer n≥1, it proves that

\[
\mathcal T_n p=(p_X-jp_Y)/n : V_n\longrightarrow W_n
\]

is a complex-linear isometric isomorphism, with inverse A-jB ↦ XA+YB,
and that dim_C W_n=n+1. There are no unproved analytic or representation-theoretic
premises. The finite-dimensional statement does not assert the discrete-series,
Hardy-space, or cohomological results.

The source is DS1, version 1, in the Math Research wiki's
`quaternionic-analysis/fueter-discrete-series.md`, using its spinor conventions
and compatible coefficient model. [The retained source](DS1-source.json) pins
the exact article and the relevant R060 argument. The researcher selected this
branch as the formalization priority after EI7.

## Small statement correspondences

All declarations below are in `MathResearch.Spinor`. These are inspectable
comparisons, without visitor approval controls or a tracked human-check status.

1. **Polynomial space.** `BinaryForm n` is exactly mathlib's
   `MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n`. Variable 0 is X; variable
   1 is Y. Homogeneity, multiplication and differentiation are mathlib's
   definitions. `exponent n k` is the exponent vector of X^(n-k)Y^k, and
   `coefficients n p k` is its ordinary polynomial coefficient. The proved
   `coefficientEquiv` identifies this whole subspace with n+1 free complex
   coefficients; it is not an assumed basis or a restricted family of polynomials.

2. **Polynomial norm.** `weightedCoefficients n` sends c_k to
   c_k/sqrt(binomial(n,k)) in mathlib's complex Euclidean space. The induced
   inner product is defined before the gradient. `binaryForm_norm_sq` proves
   exactly ‖p‖²=Σ_k |c_k|²/binomial(n,k). The binomial coefficients are positive
   on all indices used, including both endpoints. No norm is transported
   from the gradient to force the isometry.

3. **Quaternion convention and complex scalars.** `pack a b = a-jb`, where
   complex numbers use mathlib's embedding into real quaternions and
   `quaternionJ = (0,0,1,0)`. `pack_components` gives (Re a, Im a, -Re b, Im b).
   `pack_smul` proves `pack (z*a) (z*b) = pack a b * z`: this is the wiki's
   **right** complex scalar action on quaternion coefficients. The quaternion
   norm is mathlib's ordinary Euclidean norm, and `pack_norm_sq` proves
   |a-jb|²=|a|²+|b|².

4. **Rows and compatibility.** `FormRow m` is the L² direct sum of two
   `BinaryForm m` spaces, with entries A and B. `CompatibleRow m` is the
   submodule cut out by the actual polynomial equality `pderiv 1 A = pderiv 0 B`.
   It represents W_(m+1). `quaternionCoefficients_bijective` proves that *every*
   quaternion coefficient row has exactly one pair (A,B); thus using pairs
   loses no quaternion-valued polynomials. `formRow_norm_sq` identifies the
   ambient norm with Σ_k |h_k|²/binomial(m,k), independently of compatibility.
   Auxiliary X,Y are commuting polynomial variables; no claim about
   noncommuting quaternion variables is used.

5. **Map and inverse.** `derivative m i` is mathlib's `pderiv i` restricted to
   the homogeneous subspaces. `normalizedGradient m` is
   `(p_X/(m+1), p_Y/(m+1))`; its output is proved compatible using commuting
   partial derivatives. `normalizedGradient_quaternionCoefficients` proves
   the coefficientwise quaternion formula `(p_X-jp_Y)/(m+1)`.
   `assemble m` is the polynomial XA+YB. `assemble_gradient` and
   `gradient_assemble` prove the inverse laws using mathlib's Euler identity.

6. **Isometry and dimension.** `derivative_norm_sq` proves
   ‖p_X‖²+‖p_Y‖²=(m+1)²‖p‖² using the coefficient derivative formula and
   mathlib's two binomial identities. `spinorIsometry m` is a genuine
   `BinaryForm (m+1) ≃ₗᵢ[ℂ] CompatibleRow m`; this bundled mathlib type includes
   complex linearity, bijectivity and preservation of the metric.
   `finrank_compatibleRow` proves dimension m+2.

The final theorem **`DS1_v1 (n : ℕ) (hn : 1 ≤ n)`** uses the wiki's n directly.
It states existence of a complex linear isometric equivalence from `BinaryForm n`
to `CompatibleRow (n-1)`, specifies both its derivative formula and its inverse
polynomial formula, and gives dimension n+1. The internal constructive map is
indexed by m=n-1 only to avoid casts between polynomial degrees. All positive
n are covered, including the Hardy endpoint n=1.

## Sources and proof dependencies

- [BinaryForm.lean](../MathResearch/Spinor/BinaryForm.lean): actual homogeneous
  polynomial subspaces, coefficient equivalence, finite dimension and weighted
  Hermitian norm.
- [CompatibleRow.lean](../MathResearch/Spinor/CompatibleRow.lean): quaternion
  correspondence, right complex action, compatible rows and the inverse laws.
- [GradientIsometry.lean](../MathResearch/Spinor/GradientIsometry.lean): norm
  calculation, bundled isometric equivalence and DS1/v1.

The principal mathlib inputs are `MvPolynomial.pderiv`, `coeff_pderiv`,
`pderiv_comm`, `IsHomogeneous.pderiv`, `IsHomogeneous.sum_X_mul_pderiv`,
`Nat.choose_mul_succ_eq`, `Nat.add_one_mul_choose_eq`, `PiLp`,
`EuclideanSpace`, induced inner-product/normed-space structures, and
`LinearIsometryEquiv`. Lean 4.35.0 and mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` are unchanged.

The new namespace separates the spinor foundations from `MathResearch.Fueter`.
All earlier mathematical modules are preserved. The root import adds DS1 so a
normal `import MathResearch` includes both branches.

## Reproduction and evidence

From the standalone repository root:

```sh
python3 scripts/verify.py --clean-local
bash scripts/lake.sh env lean -DwarningAsError=true -DautoImplicit=false docs/DS1-statement-check.lean
```

The [statement-check source](DS1-statement-check.lean) prints the exact main
signature and checks the definitions, right scalar order, inverse, n=1 endpoint
and degree-two middle-monomial normalization. These checks are correspondence
examples, not substitutes for the all-degree proof.

The retained clean build and axiom audit is
[`evidence/DS1-v1-2026-10-31.json`](../evidence/DS1-v1-2026-10-31.json).
The separate [statement-check record](../evidence/DS1-statement-check-2026-10-31.json)
retains its command, output and fingerprints. The clean check rebuilds every
local module and audits all local declarations, including private helpers.
Allowed axioms are only `propext`, `Classical.choice`, `Quot.sound`.
Upstream pinned release caches are retained; this is not an independent rebuild
of mathlib or a second proof-kernel check. Formal proof checking does not by itself
certify fidelity to prose, significance, or the larger research branch.
