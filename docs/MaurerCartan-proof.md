# Maurer–Cartan for matrix-valued maps

This is a separate background result for the L6 inference in R060. It is not an
alternative research proof. The research theorem invokes it after the already
proved full section formula L4. This note gives the statement and actual proof
for a separate expository appendix section; it does not revise the wiki.

## Exact scope

Let E be a real normed vector space, A a finite-dimensional real normed
associative unital algebra (not necessarily commutative), and I a finite index
set. Equip M = Matrix(I,I,A) with its elementwise norm. Let f,g : E → M and x∈E.
Assume:

1. f is C² at x in mathlib's `ContDiffAt` sense.
2. g is differentiable at x.
3. g(y)f(y)=1 for all y in some neighbourhood of x.
4. f(x)g(x)=1.

Define θ(y,u)=g(y) Df(y)[u]. Then for every v,w∈E,

\[
D_v\theta(\cdot,w)(x)-D_w\theta(\cdot,v)(x)
 +\theta(x,v)\theta(x,w)-\theta(x,w)\theta(x,v)=0.
\]

The declaration is `MathResearch.Analysis.maurerCartan` in
`MathResearch/Analysis/MaurerCartan.lean`. This is the pulled-back matrix
Maurer–Cartan equation on constant vector fields. It does not construct a
bundled Lie-group differential form, require a global inverse, or assume an
unverified Maurer–Cartan equation. The explicit inverse hypotheses and
regularity hypotheses remain visible in the background statement and are
proved for the ball application.

## Proof actually formalized

Matrix multiplication is bilinear. Since M is finite-dimensional, its two
linear arguments give a continuous bilinear map (`algebraMulCLM`). Mathlib's
`ContinuousLinearMap.fderiv_of_bilinear` gives

\[
D(fg)[u]=f\,Dg[u]+Df[u]\,g.
\]

This is `fderiv_algebra_mul`; no submultiplicative elementwise matrix norm is
assumed. Differentiate the local equality gf=1 at x to get

\[
Dg[u]f+gDf[u]=0.
\]

Right-multiply by g and use fg=1. Associativity gives

\[
Dg[u]=-gDf[u]g.
\]

Apply the product rule to θ(·,w):

\[
D_v\theta(\cdot,w)=-gDf[v]gDf[w]+gD^2f[v,w].
\]

Subtract the same expression with v and w exchanged. Mathlib's
`ContDiffAt.isSymmSndFDerivAt` supplies the symmetry of D²f under the C²
hypothesis. The second derivative terms cancel, leaving the negative
commutator. Associative ring algebra completes the equation. The Lean proof
performs these steps directly. The two calculus inputs are already proved in
mathlib; there are no external mathematical assumptions.

## Application to R060 L6

Set f=σ, g=σ⁻¹, x=q in the open ball, M=Matrix(Fin 2,Fin 2,ℍ).
`ballSections_contDiffAt_two` proves C² regularity from the positive square-root
factor and the linear matrix entries. `ballSection_inverse` supplies both
inverse identities; openness of the ball makes the first a local identity.

`ballSection_maurerCartan` is the existing L4 formula for θ. Its lower-right
entry is A, and its off-diagonal entries are dq/s and dbar(q)/s. Apply the
continuous linear entry map M↦M₁₁ to the background equation. Differentiation
commutes with this map by mathlib's chain rule. L4 holds throughout a
neighbourhood, so the derivative of its lower-right entry is the derivative
of A. The lower-right product block is

\[
(\theta(v)\theta(w))_{11}
=s^{-2}\bar v w+A(v)A(w).
\]

Consequently

\[
D_v A(w)-D_w A(v)+[A(v),A(w)]
=-s^{-2}(\bar v w-\bar w v),
\]

exactly L6. `ballCurvature_eq` performs this inference. Its proof does not use
`fderiv_ballConnection`, the retained direct-differentiation helper.

## Verification and publication boundary

Use this delivery's clean-build, all-declaration axiom, exact-statement and
proof-dependency records, pinned by `SC1-SC2-correspondence.library.lock.json`.
The code and this proof note require independent correspondence review before
publication integration. This note supplies the missing background exposition
input; it does not claim that an appendix has been written or reviewed.
