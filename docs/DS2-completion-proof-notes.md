# DS2 completion: compact-support continuity, derivatives and row realization

These are internal mathematical notes from the Lean role. They expand and
verify the argument in R060, `corrected-realization.md`, sections 2–3. The
canonical file is unchanged, with SHA-256
`a68b805e519240fe45a9eb4da658546bffc3b787352b9eb2da8e0e76b79a297e`, inspected
at accepted checkout revision `8753be59dcf8725a8dd83ce905293b015030ba7c`.
The earlier partial releases and alternative proofs remain historical records.
The new source is in `formal/quaternionic-analysis-lean-ds2-continuity/`, branch
`codex/ds2-continuity`. Names below have prefix `MathResearch.Spinor`.

The goal is the canonical proof, not only its conclusion. In this continuation
the compact-support mismatch is resolved in Lean; no alternative is proposed
for incorporation into the canonical text. Neither that text nor the wiki is
edited. The new detailed arguments below supply the justifications behind the
canonical proof's brief analytic steps, for subsequent exposition if assigned.

## 1. Compactly supported continuous density inside B

The approximating class consists of continuous ambient functions F with
compact topological support contained in the **open** unit ball B. Requiring
support in B matters: compact support somewhere in the ambient quaternion
space alone is a different specification. The actual L² classes form
`compactContinuousBallClasses n`.

The measure μ=C_n(1−|q|²)^{n−2}dv on B is regular and locally finite. It is
carried by B. Apply mathlib's dense simple-function induction. For a measurable
set t of finite measure and constant c, first approximate t∩B from within by
a compact set s, making μ(t\s) small; the part outside B is null. Regularity
and local compactness provide an open neighborhood v of s whose closure lies
in B, and a compact neighborhood k of s. Apply mathlib's quantitative Urysohn
approximation inside v∩interior(k). The resulting continuous function has
topological support in k∩closure(v), hence compact support contained in B,
and approximates c1_s in L². Combine this with the small error between c1_s
and c1_t. The class is stable under addition. Simple-function density proves
`dense_compactContinuousBallClasses`.

This specializes the proof in mathlib's `ContinuousMapDense.lean`; the
adapted source retains its attribution. It does not invoke bounded-continuous
density or assert that such functions already have interior compact support.

## 2. Continuity by change of variables, then density and unitarity

Write U_g for the existing C7 action. Its genuine L² norm identity was proved
from the exact Möbius Jacobian and weight/fibre cancellation. For a continuous
compactly supported F, let f be its L² class. The inner-product convention in
the following calculation is mathlib's complex convention; only the real part
enters, so it agrees with either convention in the norm identity.

By that change-of-variables identity,

\[
\|U_gf-f\|^2=2\|f\|^2-2\operatorname{Re}\langle U_gf,f\rangle.
\]

The matrix coefficient is the integral of
⟨(π_n(g)F)(q),F(q)⟩ against μ. The integrand vanishes outside the fixed compact
set K=tsupport(F). Pointwise continuity as g→1 follows from the concrete
Möbius and polynomial formulas. Near 1 the positive denominator gap
|d|−|c| is bounded below by a fixed a>0. The exact norm formula gives
|(π_n(g)F)(q)|≤a^{−n−2}‖F‖∞ for q∈B. Thus the absolute value of the
integrand is bounded by a fixed constant times 1_K, integrable by local
finiteness. Dominated convergence gives the matrix-coefficient limit and the
displayed identity gives norm continuity at 1. The group law and unitarity
transfer it to every g. These are
`continuousAt_one_weightedL2Action_compact` and
`continuous_weightedL2Action_compact`.

All U_g are isometries, uniformly Lipschitz with constant one. Extend
continuity from the proved dense interior compact-support class using
mathlib's dense-class/Lipschitz continuity theorem. This gives
`continuous_weightedL2Representation_by_compact`; restriction gives
`stronglyContinuous_regularRepresentation_by_compact`.

This follows the canonical order: compact-support continuity using change of
variables, then density and unitarity, then restriction. Polarization is an
expanded justification of the first step, allowing a fixed compact dominating
set. The earlier bounded-continuous/finite-total-mass approximation proof is
preserved but is not used. The proof-route check traverses the actual local
proof dependencies of DS2 and checks that the four old alternative continuity
theorems are absent, while the compact density, compact continuity and
change-of-variables theorems are present. This supplements, rather than
replaces, mathematical correspondence inspection.

## 3. Interior estimates for all real derivatives and averaging

The preceding Weyl release constructs compact smoothing kernels K_r with
unit integral and proves local scale independence for distributionally
harmonic functions. A smooth harmonic u therefore satisfies
u(a)=∫K_r(a−y)u(y)dy whenever |a|+2r<1.

For an arbitrary finite list of quaternion vectors v₁,…,v_j, considered as
real directions, let P_v u=∂_{v₁}⋯∂_{v_j}u, with the first entry the
outer derivative. `realDirectionalPartials` states this convention explicitly.
Commutation of actual distribution derivatives shows that Δ(P_v u)=0;
smoothness follows by repeated Fréchet differentiation on the open ball.
Consequently the same kernel identity holds for P_v u. Repeated integration
by parts moves the derivatives onto the compact test φ(y)=K_r(a−y):

\[
P_vu(a)=\int_B \varphi_v(y)u(y)\,dy.
\]

The signed test is defined recursively by
φ_[]=φ and φ_{v::vs}=partialAdjointTest(vs,−∂_vφ).
This records the minus signs and reversal in the formal adjoint. Every test
remains smooth with compact support in B. The precise identity is
`harmonicPartials_test_formula`. This does not differentiate an arbitrary
measurable L² representative or the variable-radius selector used in Weyl's
construction.

Fix a∈B and r=(1−|a|)/4. As in the previous evaluation proof,
φ_v/w∈L²(wdv), where w=C_n(1−|q|²)^{n−2}>0 on the test's compact support.
Mathlib's Hölder pairing therefore makes the displayed integral a bounded
complex-linear map of the regular Hilbert vector. These are
`regularPartialEvaluation`, `regularPartialEvaluation_eq_representative` and
`regularPartials_bound`. The bound is valid for every finite list of real
directions and every interior point, with a finite operator-norm constant
depending on them. Coordinate mixed partials are obtained by lists from the
four-element real quaternion basis. Order zero recovers point evaluation.

For any Bochner-integrable family f_x of regular Hilbert vectors, continuous
linear maps commute with integration. Applying each partial-evaluation map
proves

\[
P_v\widetilde{\int f_x\,d\nu}(a)
 =\int P_v\widetilde f_x(a)\,d\nu(x).
\]

Here tildes denote the unique smooth representatives on B. The left integral
is taken in the complete regular Hilbert space. The family of evaluated
derivatives is integrable by the same bounded-map estimate.
`regularPartials_integral` supplies this justification of differentiation and
averaging. Its hypothesis is Hilbert-space Bochner integrability; mere
pointwise integrability is not substituted. Compact Haar averages require
their usual continuity/integrability hypotheses. The actual compact-group
averaging and irreducibility constructions of DS3 are still separate work.

## 4. The independent weak row equation and the C3 representation

The prior image-defined row kernel is now compared with a directly stated
distributional equation, in addition to the preceding smooth comparison.
For h∈L²(B,CompatibleRow(m),μ), let h_d be the actual quaternion coefficient
of A−jB at a monomial d. `RowDistributionRegular` says

\[
\sum_{\mu=0}^3 e_\mu\int_B(\partial_\mu\varphi)(q)h_d(q)\,dq=0
\quad\text{for every smooth compact test }\varphi\text{ and every }d.
\]

Local Lebesgue integrability of h and its coefficient functions is proved.
`rowWeakTest_eq_distribution` identifies the displayed expression with the
negative ordinary distributional Fueter derivative, with mathlib's actual
distributions. Thus totalized integrals cannot conceal missing integrability.

For n=m+1, the coefficient of the normalized gradient is n⁻¹ times the
existing unnormalized Fueter coefficient. Its action on test integrals gives
n⁻¹ times the quaternion packing of the two complex weak-spinor tests.
Since n≠0 and packing is injective, the two equations are equivalent.
`mem_weakRowKernel_iff_distribution` proves this for every ambient row L²
class. Together with `mem_weakRowKernel_iff_classical`, it identifies both
the independently stated weak and smooth row realizations with the Hilbert
model used in the code. Compatibility is the actual fixed polynomial
derivative constraint in `CompatibleRow`, not an assumed abstract fibre.

Transfer the actual polynomial unitary representation through the normalized
L² isometry: Π_g=𝒯 U_g 𝒯⁻¹. `regularRowRepresentation` is a group homomorphism
into complex linear isometry equivalences, and its strong continuity follows
from the new compact-support proof. This follows the canonical instruction
to prove the theorem on the polynomial model and transfer it through 𝒯.

The transported action is separately identified with the explicit C3 formula
by `regularRowRepresentation_ae`. This uses the already proved polynomial
chain rule, quaternion packing, normalized gradient, and right-transposed
coefficient action, plus quasi-invariance to transport almost-everywhere
equalities through the Möbius map. The inverse-element convention, left
quaternion factor, and right complex factors all remain visible. The
intertwiner is `regularRow_intertwining`. The C3 and C7 statements are
equalities of actual L² representatives almost everywhere; smooth
representatives are unique on B.

## 5. Exact probability normalization and completeness

The existing measure already includes C_n=n(n−1)/π². No measure or norm is
changed in this continuation. What was missing was the proof that its total
mass is one. Mathlib's radial Haar integration and four-dimensional ball
volume give the displayed radial integral in section 2. For k=n−2, use the
explicit antiderivative

\[
A(r)=\frac{(1-r^2)^{k+2}}{2(k+2)}-
     \frac{(1-r^2)^{k+1}}{2(k+1)},\qquad
A'(r)=r^3(1-r^2)^k.
\]

The fundamental theorem of calculus gives ∫₀¹r³(1−r²)^kdr
=1/[2(k+1)(k+2)]. Since vol(B⁴)=π²/2, integration of the radial weight
is π²/[(k+1)(k+2)], hence μ(B)=1. These are `radial_weight_integral`,
`integral_ballScale_pow` and `weightedBallMeasure_isProbability`. This is
the canonical radial computation, expanded without an external beta-integral
assumption.

For completeness the assembled theorem explicitly uses
`regularKernel_complete_by_localL2`, built from the prior canonical compact
L² limit argument `weakKernel_isClosed_by_localL2`. Completeness transfers
to the row model through the isometry. The earlier closed-intersection proof
remains part of historical infrastructure; it is not substituted for this
step in the assembled theorem. Nonzeroness uses the previously proved
constant-vector embedding. Smooth harmonic row representatives follow by
the fixed fibre isometry from polynomial representatives; mathlib proves
that continuous linear maps preserve harmonicity.

## 6. Assembled statement and scope

`DS2_v1 m hm`, with n=m+1 and hm:1≤m, now assembles the nonzero complete
Hilbert spaces, actual probability measure, smooth harmonic classical
representatives in both models, independent row distribution comparison,
strong continuity of the concrete unitary group homomorphisms, exact C3/C7
almost-everywhere formulas and normalized intertwining. The auxiliary
derivative and averaging theorems justify the analytic sentence in its proof.
Using m rather than n avoids coercion casts between equal polynomial degrees;
it covers exactly every n≥2, including n=2. It asserts nothing at the Hardy
endpoint n=1.

The written steps are now matched by the formal development, with the Weyl,
interior-estimate and compact-support arguments expanded as recorded here
and in the preceding internal notes. No new unproved external mathematical
premise has been added. Standard Lean axioms are checked transitively;
the exact statement and proof route are checked separately. This is author
verification and proof-correspondence inspection, not independent review.
DS3 irreducibility and DS4 square-integrability/Haar/Schur inputs remain
uninstantiated. This delivery does not certify those claims or the whole article.

The standalone guide, target record and lock file bind the clean build,
axiom audit, statement checks and proof-route check to source and canonical
proof hashes. The Coordinator is notified once for this DS2 milestone, by
mail; no intermediate lemma notifications or wiki edits are made.
