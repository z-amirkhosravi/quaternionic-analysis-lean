# Separate mean-value and quotient-Haar proofs; DS3–DS4 completion

This is the Lean role's internal mathematical proof record, dated 2026-10-31
(America/Toronto). It supplies background proofs for separate expository articles.
It does not edit the research manuscript or wiki. The companion standalone
repository is `formal/quaternionic-analysis-lean-ds3-ds4-background`, branch
`codex/ds3-ds4-background`, based on release
`377a46bd591ec859e5022183b4e252880aa104b8`.

The canonical research argument remains R060, `corrected-realization.md`, §§4–5,
SHA-256 `a68b805e519240fe45a9eb4da658546bffc3b787352b9eb2da8e0e76b79a297e`.
Its exact passage is retained in `docs/DS3-DS4-proof-source.json`. The accepted
checkout inspected at entry was `8753be59dcf8725a8dd83ce905293b015030ba7c`;
the shared checkout was `22a584d537373ef8d4aea95b3bd0dfe0acca8929`.
These identify inspected inputs, not an instruction to integrate either tree.

## 1. Spherical mean values in real dimension four

**Precise scope.** Let E be any complete real normed vector space. Let
F : ℍ → E be smooth on B={q: |q|<1} and harmonic there in mathlib's sense
(`ContDiffOn ℝ ∞`, `InnerProductSpace.HarmonicOnNhd`). Let da be Haar
probability on the actual group of unit quaternions. Then, for every q∈B,

\[
\int_{\operatorname{Sp}(1)}F(a^{-1}q)\,da=F(0).
\]

There is no global integrability hypothesis: the averaging orbit is compact
inside B. This release does not claim all dimensions, arbitrary balls, weak
harmonic inputs, or the minimal C² formulation. The exact statement is
`SphericalMeanValueOnBall`, proved by `sphericalMeanValueOnBall_proved` in
`Analysis/QuaternionicMeanValue.lean` (namespace `MathResearch.Spinor`).

**Proof.** First use the average A(q)=∫F(aq)da. Compact Haar probability is
right invariant and inversion invariant. These facts are proved separately in
`CompactHaarSymmetry.lean` from mathlib's uniqueness of normalized Haar measure;
they are not assumed additional measure properties.

On any smaller closed ball about a point of B, the rotated function and its
first two derivatives are jointly continuous on a compact product. Their
norms are bounded by an integrable constant on the compact index group.
Mathlib's differentiation-under-the-integral theorem therefore gives

\[
DA(q)v=\int DF(aq)(av)\,da,\qquad
D^2A(q)(v,w)=\int D^2F(aq)(av,aw)\,da.
\]

The compact-parameter differentiation lemma is independently stated in
`CompactParametricIntegral.lean`. The two applications, with actual continuous
linear maps as derivatives, are in `QuaternionicSphericalAverage.lean`.
Left multiplication by a unit quaternion is a real linear isometry. Summing
the Hessian on an orthonormal basis and using mathlib's basis-independent
Laplacian formula shows ΔA(q)=∫ΔF(aq)da=0.

Right invariance of da gives A(bq)=A(q) for every unit b. Normalizing any
nonzero q gives A(q)=M(|q|), where M(r)=A(r·1). At the origin, the derivative
vanishes: change a to −a in the derivative integral. For r>0 the radial Hessian
has radial entry M″(r) and each of the three unit tangential entries M′(r)/r.
To justify the tangential computation, differentiate
DA(q)v=(⟨q,v⟩/|q|)M′(|q|); at ⟨q,v⟩=0 the second term vanishes, leaving
D²A(q)(v,v)=|v|²M′(|q|)/|q|. Thus

\[
M''(r)+3M'(r)/r=0\quad(0<r<1).
\]

`RadialHessian.lean` proves that Hessian calculation; `RadialHarmonic.lean`
computes its trace. In the separate `RadialMeanODE.lean`, differentiation gives
(r³M′(r))′=0. Regularity at zero forces the constant to be zero, so M′=0 on
[0,1), and M(r)=M(0). The proof uses mathlib's vector-valued zero-derivative
constancy theorem, without an assumption of finite-dimensional E. Finally
A(0)=F(0) by completeness and total mass one, and Haar inversion invariance
converts F(aq) to the requested F(a⁻¹q).

This is an explicit background proof now supplied for a theorem previously
cited without proof. It does not replace the compact-averaging research argument.

## 2. Weighted radial mean values

**Precise scope.** For n≥2 set s(q)=1−|q|²,
C_n=n(n−1)/π², and dμ_n=C_n s(q)^(n−2)1_B(q)dq. For F as in §1, additionally
assume F∈L¹(μ_n). Then ∫F dμ_n=F(0).
`radialMeanValueOnBall_proved` in `QuaternionicRadialMeanValue.lean` proves the
exact interface `RadialMeanValueOnBall`; the target space is again any complete
real normed space. The endpoint n=1 is not included.

**Proof and recorded proof choice.** The prior `ProbabilityMeasure.lean`
already proves μ_n(B)=1 by explicit radial integration. On the ball subtype,
left unit rotations preserve Lebesgue measure by mathlib's measure-preservation
theorem for real linear isometries. They preserve the density since |aq|=|q|.
`InvariantDensity.lean` states the general measure-preserving weighted-density
lemma; `RotationalBallMeasure.lean` applies it and transfers the established
probability normalization to the ball subtype.

For every a, ∫F(aq)dμ_n(q)=∫F(q)dμ_n(q), and the same holds for the norm.
Joint continuity and ∫∫|F(aq)|dμ_n da=∫|F|dμ_n<∞ establish product
integrability. Fubini and §1 now give

\[
\int_B F(q)d\mu_n(q)
=\int_B\int_{\operatorname{Sp}(1)}F(aq)da\,d\mu_n(q)
=\int_B F(0)d\mu_n(q)=F(0).
\]

The earlier dependency inventory called this a polar-integration corollary.
Here the angular averaging is performed by rotation invariance and Fubini;
polar integration is used through the existing proof of total mass one. This
is the detailed background proof chosen for the new exposition. No research
inference is changed: its reference remains the weighted harmonic mean-value
theorem. The L¹ and product-integrability steps are explicit, so no totalized
Bochner integral is used to disguise a divergent integral.

## 3. Normalized quotient-Haar integration for Sp(1,1)

**Precise scope.** Let G be the actual quaternion matrix group Sp(1,1),
K=Sp(1)×Sp(1), dk the product of Haar probabilities, and σ the already specified
ball section. There is a concrete left Haar measure dg with

\[
\int_G\phi(g)dg
=\int_B s(q)^{-4}\int_K\phi(\sigma(q)k)dk\,dq.
\]

The checked interface quantifies over **nonnegative continuous real-valued φ**
and includes equivalence of integrability of the two sides. A preceding
nonnegative extended-integral theorem establishes Tonelli's identity without a
finiteness assumption. This is the Sp(1,1) theorem needed for coefficient
norm-squares, not a claim of the general Weil formula for arbitrary groups.
`quotientHaarIntegration_proved` proves
`QuotientHaarIntegration normalizedGroupHaar` in `QuaternionicQuotientHaar.lean`.

**Coordinates.** Every g has the unique decomposition g=σ(g·0)k. The existing
matrix factorization supplies k's two unit quaternion entries. Conversely,
σ(q)k has origin q; cancellation then recovers k. The explicit formulas and
their inverses are continuous. `QuaternionicHaarCoordinates.lean` packages
them as `groupBallHomeomorph : G ≃ₜ B×K`. With
c(g,q)=the compact coordinate of gσ(q), multiplication satisfies

\[
g\sigma(q)k=\sigma(gq)c(g,q)k.
\]

**Invariant base measure.** Put dν(q)=s(q)⁻⁴dq on B. The earlier verified
Möbius formulas give s(gq)=s(q)/|cq+d|² and real Jacobian |cq+d|⁻⁸.
Consequently s(gq)⁻⁴|cq+d|⁻⁸=s(q)⁻⁴. Apply the already proved change-of-variables
theorem to nonnegative measurable functions to obtain g_*ν=ν.
`QuaternionicInvariantMeasure.lean` proves the density identity and measure
equality, with local finiteness, sigma-finiteness and positivity on open sets.
ν itself is not a finite measure.

**Haar construction.** Define dg as the pushforward of ν×dk by (q,k)↦σ(q)k.
For a nonnegative measurable test function, Tonelli and the coordinate identity
first remove c(g,q) by compact left-Haar invariance, then remove gq by invariance
of ν. Thus left translation preserves dg. The homeomorphism carries compact
sets back to compact sets, so dg is finite on compacts; continuous surjectivity
and positivity of the product measure give positivity on nonempty open sets.
These prove mathlib's `Measure.IsHaarMeasure`, not merely an integration formula
for an arbitrary measure. The construction is `normalizedGroupHaar` and the
instance is `normalizedGroupHaar_isHaar`, in `QuaternionicHaarMeasure.lean`.

**Integration and finiteness.** Pushforward integration and Tonelli give the
extended integral identity. Each compact fibre integral of continuous φ is
finite. Convert that inner integral using nonnegativity, multiply by s⁻⁴ and
pass between the subtype and restricted Lebesgue measure. This is
`lintegral_quotientHaarAverage`. Strong measurability and equality of the
extended nonnegative integrals prove `integrable_quotientHaar_iff`.
Only then is the real Bochner equality packaged as `integral_quotientHaar`.
The integrability equivalence remains available when either side diverges.

## 4. Completing the research argument without moving its background proofs

All 98 prior mathematical modules are preserved byte for byte. In particular,
the research modules `DiscreteSeriesIrreducible`, `RegularCoefficient`,
`RegularSquareIntegrable` and `DiscreteSeriesCoefficient` retain their proofs.
`DiscreteSeriesVerified.lean` supplies the newly proved background theorems to
their existing explicit arguments. The old conditional signatures remain useful
and keep their historical records; they are no longer the final target claims.

DS3 uses spherical mean values exactly at C11, followed by detection of a
nonzero translate, compact irreducibility of constants, and the orthogonal
complement argument. The separately verified compact irreducibility theorem is
still invoked, not inlined. `DS3_v1` and `DS3_row_v1` assert irreducibility and
density of translates of constants in the polynomial and compatible-row models.

DS4 uses weighted mean values for the constant pairing, the exact C12 lift
identification and intertwining, quotient-Haar integration and the separately
verified Schur formula. It obtains genuine square integrability and

\[
\|\mathcal W_v f\|_{L^2(G)}^2
=\frac{\|v\|^2}{(n+1)C_n}\|f\|_{\mathcal B_n}^2.
\]

`DS4_v1` gives the actual coefficient map, its almost-everywhere coefficient
formula, this norm identity, injectivity, closed image, intertwining and
invariant range. `DS4_polynomialEmbedding` and `DS4_rowEmbedding` are normalized
linear isometries; `DS4_row_v1` supplies the row closed-image and intertwining
claims. `DS4_coefficient_formula` records L² membership and C13 even for v=0.
Mathlib's inner product is linear in the second slot, so the written linear-first
coefficient is represented with the two arguments reversed, as before.

All research degrees are n=m+1 with m≥1, hence n≥2. Together these verify the
stated discrete-series realization as an irreducible unitary representation
embedded with closed invariant image in left Haar L². No classification theorem
or additional external mathematical assumption is used. No claim is made here
about the n=1 Hardy endpoint, later K-type assertions, or other research claims.

## 5. Evidence and exposition handoff

The standalone `docs/DS3-DS4-verified.md` gives replay commands and scope.
The statement check prints the exact interfaces, definitions and unconditional
research signatures; its examples contain no mean-value or Haar premise.
The proof-route check follows actual transitive local dependencies, requiring
the new named background proofs and the canonical DS2 compact-support
continuity route and excluding the previously superseded continuity alternative.
Source preservation, a clean local build, and the all-declaration axiom audit
are saved with fingerprints in `evidence/DS3-DS4-verified-*` and indexed by
`formal/DS3-DS4-verified.library.lock.json`.

The correspondence inspection is author self-check, not independent review.
Kernel verification checks the precise Lean statements; the internal step map
explains their relationship to the written proof. The old ten-topic exposition
inventory remains historical; its two pending mean-value/Haar topics are now
supplied by §§1–3 above. Generic compact differentiation and the radial ODE are
also separately named and can be linked from the mean-value article. Claims
about general compact groups or general quotient-Haar integration must not be
labelled verified by these specialized declarations.

Coordinator receives one milestone mail with source revisions and evidence.
Any accepted-source integration and wiki exposition remain separate and await
the researcher's instruction.
