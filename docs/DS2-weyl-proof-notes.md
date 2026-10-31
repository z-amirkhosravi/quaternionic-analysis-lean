# DS2: Weyl regularity and the regular Hilbert action

These are internal mathematical proof notes from the Lean role. They expand
the Weyl and evaluation steps of R060, `corrected-realization.md`, section 3,
and record the status of the subsequent model and action comparisons. They
do not revise that canonical text or its wiki exposition. The canonical file
at accepted revision `8753be59dcf8725a8dd83ce905293b015030ba7c` has SHA-256
`a68b805e519240fe45a9eb4da658546bffc3b787352b9eb2da8e0e76b79a297e`;
the exact section is retained in the library's `docs/DS2-proof-source.json`.

The new sources are in `formal/quaternionic-analysis-lean-ds2-weyl/`, branch
`codex/ds2-weyl`. Declaration names below are in `MathResearch.Spinor`.
This is an author correspondence record, not an independent review or an
approval mechanism for visitors.

## 1. The precise regularity claim

Let B be the open unit ball in the Euclidean quaternion space, with ordinary
Lebesgue volume. Let E be a complete real normed space, and let u:B→E be
locally Bochner integrable. If its ordinary distribution satisfies Δu=0,
then u agrees almost everywhere on B with a smooth harmonic function.
The Lean theorem `smooth_harmonic_representative` uses mathlib's
`Distribution.ofFun`, `ContDiffOn ℝ ∞`, and `HarmonicOnNhd`. Functions are
represented on the ambient quaternion space; values outside B impose no
condition and do not affect the conclusion.

The previous release already proved distributional harmonicity of the weak
Fueter kernel by applying the conjugate operator and using injectivity of
T_n. That route is retained. `weylRegularityOnBall` now proves the exact
formerly undischarged proposition, and `weakKernel_smoothRepresentative`
applies it. No Weyl theorem is postulated or supplied as a theorem parameter
to these new conclusions. The finite-dimensional coefficient spaces are
complete by mathlib.

## 2. A full proof of the Weyl step

The canonical notes invoke Weyl's lemma without giving a proof of that
general lemma. The following construction expands that invocation. It does
not replace the surrounding conjugate-Fueter argument.

Choose mathlib's smooth cutoff χ on the real line with χ=1 on |s|≤1 and
χ=0 on |s|≥2. Define h(s)=(χ(s)−1)/s, taking its totalized value at zero.
It is identically zero near zero and therefore smooth everywhere. In real
dimension four, the chain rule and an orthonormal quaternion basis give

\[
\Delta h(|q|^2)=8h'(|q|^2)+4|q|^2h''(|q|^2)
               =4\chi''(|q|^2).
\]

Put P(q)=h(|q|²) and κ(q)=χ''(|q|²). Both are smooth; κ is supported in
the closed ball of radius 2 (a deliberately loose bound). P(q)=−|q|⁻²
when |q|≥2. The mass computation is explicit, not an assumed distributional
fundamental-solution identity. Radial Haar integration in dimension four
and the fundamental theorem of calculus give

\[
\int_0^\infty r^3\chi''(r^2)\,dr
 =\left[\frac{r^2\chi'(r^2)-\chi(r^2)}2\right]_0^2=\frac12,
\qquad M:=\int_{\mathbb H}\kappa=2\,\operatorname{vol}(B)>0.
\]

Set K=κ/M and, for r>0, K_r(q)=r⁻⁴K(q/r), P_r(q)=r⁻²P(q/r).
Then ∫K_r=1, supp K_r⊆closedBall(0,2r), and ΔP_r=4M K_r.
Outside radius 2r, P_r(q)=−|q|⁻², independently of r. Thus P_r−P_s
is a smooth compactly supported function, supported in radius 2max(r,s).
These identities are `laplacian_weylScaledPotential`,
`weylScaledPotential_tail`, and `integral_weylScaledKernel`.

Define S_r u(a)=∫K_r(a−y)u(y)dy. If
|a|+2max(r,s)<1, then y↦(P_r−P_s)(a−y) is an actual smooth compactly
supported test function in B. Testing Δu=0 against it gives
4M(S_r u(a)−S_s u(a))=0. Since M>0, S_r u(a)=S_s u(a).
`weylSmooth_eq_of_distributionLaplacian_zero` proves this with the support
and integrability obligations included. Reflection and translation of the
Laplacian are proved explicitly.

The kernels are signed. Positivity is neither asserted nor used. Compact
support and boundedness of K give
|K_r(q)|≤C/vol(closedBall(0,2r)). With r_k=1/(k+1), mathlib's
Besicovitch Lebesgue differentiation theorem and its signed-kernel integral
convergence theorem show S_{r_k}u(a)→u(a) at almost every Lebesgue point,
first for globally locally integrable functions.

For the local problem, cut u off to a closed ball of radius R<1. That cutoff
is globally integrable. On each smaller ball of radius S<R, choose
r=(R−S)/4. The support bound identifies its smoothing with the original
local integral. Scale independence identifies all sufficiently small
smoothings there. Define

\[
v(a)=S_{(1-|a|)/4}u(a),\qquad a\in B.
\]

On every smaller ball v equals one fixed-radius convolution of the integrable
cutoff. Mathlib's smooth convolution theorem proves v smooth there. We do
not differentiate the nonsmooth scale selector |a|. At almost every point
the same fixed value is the limit u(a). A countable covering by rational
radii proves u=v almost everywhere on all of B. These steps are
`weylRepresentative_eq_on_ball`, `contDiffOn_weylRepresentative`, and
`ae_weylRepresentative`.

Finally, integration by parts twice identifies the distributional Laplacian
of a smooth function with the distribution of its actual Euclidean Laplacian.
The distributional equation passes from u to v using their almost-everywhere
equality. Injectivity of the locally integrable-function distribution, then
continuity on the open ball, implies Δv=0 pointwise. This is
`harmonicOnNhd_of_smooth_distributionLaplacian_zero`. Thus the conclusion is
harmonicity as well as smoothness; the recovery and uniqueness issues are
not left as assumptions.

## 3. Classical and weak Fueter equations

For each polynomial coefficient and each of its two complex components,
integration by parts identifies the old weak test with minus the integral
of the classical first-order symbol against the test function. Packing the
two components gives exactly `Fueter.leftOperator` applied to the existing
`fueterCoefficientCLM`; signs and the A−jB convention are unchanged.
Distribution injectivity and continuity prove the converse implication.

`mem_weakKernel_iff_classicalFueter` therefore compares the actual weak
kernel with the classical coefficientwise equation for any smooth
almost-everywhere representative. Combining it with Weyl produces
`weakKernel_classicalRepresentative`. This is a bridge for the existing
definitions, not a replacement definition of regularity.

The row space is also stated independently:
`HasClassicalRowRepresentative` requires a smooth function into the actual
`CompatibleRow m` fibre, every monomial coefficient of A−jB to satisfy the
Fueter equation, and weighted almost-everywhere equality to the row L²
class. Homogeneity is already part of the fibre, so coefficients outside
its fixed degree vanish. The normalization identity is
rowCoefficient(𝒯_{m+1}p)=(m+1)⁻¹ fueterCoefficient(p).
Since m+1 is nonzero, this preserves the equation in both directions.
`mem_weakRowKernel_iff_classical` identifies this independently specified
smooth space with the previous image-defined weak row model. It does not
define the smooth condition to be that image. Existing completeness,
nonzeroness and the fibre/L² isometry can consequently be used for this
smooth realization.

## 4. The regular action follows the canonical covariance route

Take the smooth representative, apply the already proved SC3 lift/Schmid
covariance to the exact C7 formula, and use the classical/weak equivalence
to return to the weighted L² class. The action's smoothness and the
almost-everywhere representative formula are proved. This gives
`weightedL2Action_mem_weakKernel` with no regularity premise.

`regularRepresentation` is an actual group homomorphism into the complex
linear isometry equivalences of the regular Hilbert space. Its inverse is
the action of g⁻¹; its group law and norm law are inherited from the actual
ambient action. `stronglyContinuous_regularRepresentation` proves orbit
continuity in this space. The canonical instruction to restrict the ambient
action to the closed invariant kernel is now implemented.

There remains a substantive inherited proof difference: the ambient
continuity theorem uses bounded continuous approximation, a uniform local
bound on the multiplier and dominated convergence using finite weighted
mass. The canonical notes say compactly supported continuous approximation,
then density and unitarity. The alternative and its detailed justification
are preserved in `DS2-analytic-proof-notes-2026-10-31.md`. Restricting that
checked alternative does not verify the canonical approximation argument.
No change to the canonical notes or wiki is made by this delivery.

## 5. Bounded evaluation, and the boundary of this result

At a∈B choose r=(1−|a|)/4 and φ(y)=K_r(a−y). Scale independence and
uniqueness imply v(a)=∫φ(y)f(y)dy for every continuous representative v
of the regular class f. For w(y)=(1−|y|²)^{n−2} on B, the function
φ/w is continuous and compactly supported in B because w>0 there. Hence
φ/w belongs to L²(w dy). Mathlib's L² Hölder pairing makes

\[
f\longmapsto\int_B (\varphi/w)f\,w\,dy
            =\int_B\varphi f\,dy
\]

a bounded complex-linear map. This gives `regularEvaluation`,
`regularEvaluation_eq_representative`, and `regularEvaluation_bound`.
It is the pointwise interior estimate cited by the notes, derived from the
local harmonic smoothing formula rather than imported as an additional
external estimate. Evaluation of an arbitrary L² representative is not
claimed to be well-defined.

This delivery does not prove all higher-order interior derivative estimates
or differentiation and averaging under arbitrary parameter integrals. The
canonical sentence asserting those further consequences remains an open
proof obligation. The full independent row-action bundle with its exact
C3 formula, the normalized measure bookkeeping, and a consolidated full
DS2 signature also remain to be assembled and checked; prior pointwise
C3/C7 intertwining is preserved. DS3's compact averaging and irreducibility
inputs and DS4's Haar/Schur and coefficient-realization inputs remain
uninstantiated. No full DS2, DS3 or DS4 verification is claimed.

## 6. Reused foundations and evidence

The proof uses mathlib's ordinary distributions and test functions,
orthonormal-basis Laplacian, smooth bump functions, real calculus and the
fundamental theorem of calculus, radial Haar integration, smooth convolution,
Besicovitch differentiation, Bochner integration by parts, L² Hölder pairing,
Lp spaces and continuous linear maps. The project supplies the explicit
four-dimensional kernel construction and the quaternionic model bridges.

There are no new unproved external mathematical premises in these new
theorems. Standard Lean axioms are audited transitively; hypotheses and
proof correspondence are inspected separately. The target record and lock
file bind the saved build and statement checks to source commits and to this
internal note. Earlier proofs and their evidence retain their prior scope.
