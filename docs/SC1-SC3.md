# SC1/v1 and SC3/v1: connection, lift, and kernel correspondence

This development proves the ball connection and curvature, its moving-frame
derivative, the exact weighted Schmid–Fueter identity, the global equivalence
of kernels, and covariance under the explicit polynomial-spinor Möbius action.
It covers every degree n≥1, including n=1, and every polynomial coefficient.
The smooth lift and inverse section formulas are also verified.

The [source snapshot](SC1-SC3-source.json) retains the exact accepted SC1/v1 and
SC3/v1 text, conventions, DS-C1 action formula, and selected R060 notes. It is
separate from the [compiler statement checks](SC1-SC3-statement-check.lean).
These small comparisons let each reader inspect the translation. There is no
visitor approval state or human gate.

## Exact conclusions

`MathResearch.Spinor.SC1_v1` in
[GroupKernel.lean](../MathResearch/Spinor/GroupKernel.lean) takes a degree m+1
polynomial-valued function F, right K-equivariance on G, differentiability at
each group point, and q in the ball. It proves the entire Maurer–Cartan matrix,
the curvature formula in every pair of real directions, and

\[
(\xi_vF)(\sigma(q))=s\,\partial_v(F\circ\sigma)(q)
  +d\tau_{m+1}(C_v)F(\sigma(q)).
\]

Here m ranges over all natural numbers. The assumptions do not contain a
connection identity, curvature identity, or differential-equivariance premise.
`SC1_section_v1` is the equivalent constructive result for the canonical lift
of differentiable section data U.

`MathResearch.Spinor.SC3_v1` in
[FullLift.lean](../MathResearch/Spinor/FullLift.lean) takes n≥1 and a ball spinor
f differentiable at each point of the ball. Its two conclusions are

\[
24(\mathscr D F_f)(\sigma(q))=s(q)^{(n+4)/2}D_l(T_nf)(q),\qquad
\mathscr DF_f=0\text{ on }G\ \Longleftrightarrow\ D_l(T_nf)=0\text{ on }B.
\]

The identity is an equality of actual quaternion coefficients at **every**
exponent vector `Fin 2 →₀ ℕ`. No finite-degree sampling or assumed analytic
identity is used. The lift is the precise L2 formula
F_f(g)=|d|⁻²τ_n(d⁻¹)f(bd⁻¹), not an unspecified function satisfying the desired
conclusion. Its section value is s^((n+2)/2)f. The intermediate unweighted
formula is sD_l(T_nU)+(n+2)qT_nU.

`SC3_representation_covariance_v1` in
[BallAction.lean](../MathResearch/Spinor/BallAction.lean) proves preservation of
that Fueter kernel by C7:

\[
(\pi_n(\gamma)f)(q)=|cq+d|^{-2}\tau_n((cq+d)^{-1})
 f((aq+b)(cq+d)^{-1}),\qquad
\gamma^{-1}=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
\]

`SC3_smooth_correspondence_v1` in
[SmoothCorrespondence.lean](../MathResearch/Spinor/SmoothCorrespondence.lean)
proves smoothness and both inverse formulas for restriction to the section,
removal of its weight, and L2. This set-theoretic/smooth correspondence also
holds at degree zero; the differential kernel theorem requires n≥1.

## Small definition correspondences

All names below are in `MathResearch.Spinor`, unless qualified otherwise.

1. **Underlying polynomials and quaternions.** `BinaryForm n` remains DS1's
   mathlib homogeneous degree-n `MvPolynomial (Fin 2) ℂ` submodule with its
   weighted norm. The unchanged SC2 `polynomialRepresentation` is the bundled
   matrix-monoid representation p(X,Y)↦p(aX+cY,bX+dY). `quaternionMatrix` is
   the exact embedding ι(t+ix+jy+kz)=[[t+ix,y+iz],[-y+iz,t-ix]]. The column
   (A,B) represents A−jB. The algebra-homomorphism and multiplication-order
   proofs are reused, as is the genuine analytic infinitesimal action.

2. **Ball and section.** In
   [BallConnection.lean](../MathResearch/Spinor/BallConnection.lean),
   `ballScale q=1-Quaternion.normSq q` and `Ball={q | 0<ballScale q}`.
   `mem_ball_iff` proves this is ‖q‖<1. `ballSection q` is
   (√s)⁻¹•[[1,q],[conj q,1]]. Its inverse and its real Fréchet derivative are
   proved. `ballSection_maurerCartan` proves all four blocks of L4, including
   the derivative of the scalar square-root factor.

3. **Connection and curvature.** `connectionCoefficient q v` is
   C_v=(conj(v)q−conj(q)v)/2. `ballConnection q v=s⁻¹•C_v` is A(v).
   `ballCurvature q v w` is the actual derivative difference
   ∂_v(A(w))−∂_w(A(v)) plus A(v)A(w)−A(w)A(v).
   `ballCurvature_eq` proves −s⁻²(conj(v)w−conj(w)v).
   `ballCurvature_origin` evaluates it to −2i on (1,i) at q=0.
   [CurvatureWitness.lean](../MathResearch/Spinor/CurvatureWitness.lean)
   proves its action on X^(m+1) is −2i(m+1)X^(m+1) and is nonzero for every m.
   Thus the result does not flatten the connection.

4. **Actual matrix group and decomposition.** In
   [Sp11.lean](../MathResearch/Spinor/Sp11.lean), `signatureAdjoint g` is Jg*J,
   J=diag(1,−1). `IsSp11 g` means both (Jg*J)g=1 and g(Jg*J)=1, the inverse
   equations for Sp(1,1). Closure and inversion are proved. `compactMatrix a b`
   is diag(a,b), with both quaternion norms one when used as K. `groupOrigin g`
   is bd⁻¹. Its membership in B, d≠0, and s(bd⁻¹)=|d|⁻² are proved.
   `section_compact_decomposition` proves g=σ(g·0)diag(k_L,k_R), where
   k_L=√s•a and k_R=√s•d; both have norm one.

5. **Lift, inverse, and real weights.** `frameLift n U g=τ_n(k_R⁻¹)U(g·0)`.
   `fullLift n f g=normSq(d)⁻¹•τ_n(d⁻¹)f(g·0)` is L2.
   `frameLift_weighted_eq_fullLift` proves their equality on G when
   U=s^((n+2)/2)f, using a proved scalar homogeneity law τ_n(r)=r^n Id.
   `ballWeight β q=(ballScale q)^β` uses mathlib's real power; division by 2
   is real division, not natural-number division. `unweightedSpinor` uses
   exponent −(n+2)/2. `fullLift_section`, `unweight_weight`, `weight_unweight`,
   and `fullLift_recover` verify both inverse maps on their domains.
   `RightEquivariant n F` states F(g diag(a,b))=τ_n(b⁻¹)F(g) for actual
   group g and unit a,b. `fullLift_rightEquivariant` proves it for L2.

6. **Derivatives and the group-function model.** `rightLieDerivative n F g v`
   is the actual real derivative along g+t(gξ_v), ξ_v=[[0,v],[conj v,0]].
   `rightLieDerivative_eq_exp` proves equality with the wiki's
   derivative along g exp(tξ_v). `rightLieDerivative_congr_on_group` proves
   independence of the representative away from G, using the group curve
   gσ(tv). Thus a straight ambient tangent line does not introduce a choice
   of off-group derivative into the result.

   Group functions are represented by maps on the ambient quaternion matrix
   space, with differentiability or `ContDiffAt ℝ ∞` required only at group
   points. Ball functions are maps on ℍ with regularity required only in B.
   All conclusions and inverse identities are restricted to those domains;
   arbitrary outside values are not identified. The explicit L2 formula
   supplies the required smooth representatives. A bundled Lie-group/manifold
   API, quotient of representatives, and comparison with mathlib's manifold
   `ContMDiff` are not introduced or claimed here. The exact regularity
   predicates are printed in the statement-check output.

7. **Projection and normalization.** `fueterCoefficientCLM n d` is the real
   continuous linear map extracting the d-th coefficient of unnormalized
   T_np=p_X−jp_Y. `projectedGroupOperator` sums vT_n(ξ_vF) over the unchanged
   ordered `Fueter.coordinateBasis` (1,i,j,k). `schmidOperator` multiplies by
   1/24, and the normalization equation is proved. No DS1 division by n enters.

8. **Global kernel and covariance.**
   [OrthonormalContraction.lean](../MathResearch/Spinor/OrthonormalContraction.lean)
   proves basis independence of the bilinear contraction using mathlib's
   orthonormal bases. [SchmidCovariance.lean](../MathResearch/Spinor/SchmidCovariance.lean)
   proves the projected symbol's K-transformation, using the actual EI7 unit
   quaternion rotations and SC2 polynomial chain rule. Together with the
   proved group decomposition it extends section vanishing to every g∈G.
   [GroupKernel.lean](../MathResearch/Spinor/GroupKernel.lean) proves left
   translation commutes with the operator. `fullLift_section_translate` and
   `fullLift_ballAction` prove that this translation is exactly C7.
   `ballRepresentation` inserts `signatureAdjoint γ`, already proved to be
   γ⁻¹ on G; its denominator is cq+d in that inverse matrix.

## Proof, mathlib reuse, and remaining scope

The new analytic steps use mathlib's real Fréchet derivatives, composition and
product rules, square-root and real-power derivatives, matrix exponential,
finite-dimensional continuous linear maps, smooth inversion in complete
normed algebras, and orthonormal-basis expansions. The polynomial and quaternion
objects are reused from mathlib through the existing DS1/SC2/EI7 development.
The weight cancellation is proved by differentiating s^β, with β=(n+2)/2;
the term −2βqT_nf cancels the proved SC2 connection term (n+2)qT_nf.
No unformalized Liu–Zhang theorem or requested conclusion is an axiom/premise.

This delivery does not prove the Hilbert-space, measure/Jacobian, strong
continuity, unitarity, irreducibility, compact-type, boundary-trace, or
cohomological assertions in the research articles. In particular covariance of
C7 is not the whole DS2 theorem, and no full unitary group representation on
its completed function space is claimed. Earlier mathematical modules and
pinned dependencies remain unchanged.

## Reproduction and evidence

Lean 4.35.0 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned.
From this standalone checkout:

```sh
python3 scripts/verify.py --clean-local
bash scripts/lake.sh env lean -DwarningAsError=true -DautoImplicit=false docs/SC1-SC3-statement-check.lean
```

The clean audit is retained at
[evidence/SC1-SC3-v1-2026-10-31.json](../evidence/SC1-SC3-v1-2026-10-31.json).
It fingerprints every checked source/configuration/checker file and audits
transitive axioms of public, private, and generated local declarations.
The allowed axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`;
`sorryAx`, new axioms, and native decision shortcuts are rejected.
[Statement evidence](../evidence/SC1-SC3-statement-check-2026-10-31.json) retains
the command, compiler output, script hash, and audited input fingerprints.
Upstream caches are retained: this is a clean rebuild of the local library,
not an independent rebuild of mathlib or a second proof-kernel check.
