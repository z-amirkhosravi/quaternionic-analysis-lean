# DS2 analytic continuation

This continuation proves distributional harmonicity of the actual weighted
weak Fueter kernel and constructs a strongly continuous unitary action on the
ambient weighted L² space. It also implements the canonical local L² proof
of closedness. **Full DS2 and its complete written proof remain unverified.**

The canonical mathematics is R060's corrected realization, section 3, whose
DS2 exposition is in the discrete-series article. The
[source record](DS2-proof-source.json) fingerprints the internal proof,
expository proof and statement separately. The
[correspondence audit](DS2-proof-correspondence.md) maps their substantive
steps to declarations and retains every unresolved step or difference.

## Checked unconditional results

All declarations are in `MathResearch.Spinor`, for every natural n≥2.

- [WeightedLocalization](../MathResearch/Spinor/WeightedLocalization.lean)
  identifies weighted L² classes with ordinary locally integrable
  distributions using mathlib's `Distribution.ofFun`; the association is
  injective.
- [WeakHarmonic](../MathResearch/Spinor/WeakHarmonic.lean) proves the conjugate
  Fueter factorization and injectivity step of the canonical proof. It uses
  mathlib test functions, distribution derivatives, Hessian symmetry and the
  Euclidean Laplacian. The concluding declaration is
  `weakKernel_distributionLaplacian_zero`.
- [LocalL2](../MathResearch/Spinor/LocalL2.lean) proves the compact lower bound
  on the density and continuous restriction to ordinary L²(K).
  [LocalClosure](../MathResearch/Spinor/LocalClosure.lean) passes the actual
  test equation to limits in these local spaces. Its
  `weakKernel_isClosed_by_localL2` repairs the earlier proof-route difference.
- [MobiusMeasure](../MathResearch/Spinor/MobiusMeasure.lean) proves the
  Jacobian identity as an equality of measures and the pullback of null sets.
  [WeightedL2Action](../MathResearch/Spinor/WeightedL2Action.lean) proves
  actual square-integrability, representative independence, linearity, norm
  preservation, the cocycle group law and inverses. The bundled action is
  `weightedL2Representation n hn : Sp11 →* (BallL2 n ≃ₗᵢ[ℂ] BallL2 n)`.
- [L2StrongContinuity](../MathResearch/Spinor/L2StrongContinuity.lean) proves
  joint continuity of that concrete action and, in
  `stronglyContinuous_weightedL2Representation`, continuity of each orbit.
  No regularity, kernel-invariance or abstract representation hypothesis is
  assumed for this ambient result.

## Proof correspondence and the alternative continuity argument

The target is the written argument, not just a theorem with the same conclusion.
The internal notes are the mathematical source; a wiki article is its exposition.
Lean work does not revise the wiki to match its code. Necessary alternative
arguments are recorded internally for mathematical reconciliation and later,
separately assigned exposition. There is no visitor approval state or human gate.

The local-limit closedness proof and the direct cocycle proof have now been
implemented to match the canonical route. Earlier checked alternatives are
preserved, not represented as verification of those written steps.

Strong continuity uses a documented alternative: approximate by **bounded
continuous functions**, using mathlib's density theorem for finite measures,
instead of the canonical compact-support class. For g⁻¹ with bottom row (c,d),
the group equation gives |d|²−|c|²=1. Hence δ(g)=|d|−|c| is continuous and
positive, and |cq+d|≥δ(g) throughout B. Near g₀ set a=δ(g₀)/2>0. The exact
multiplier norm bounds |U_gF(q)| by M=a^(−n−2)‖F‖∞. Pointwise continuity in
g and the integrable constant bound 4M² yield L² convergence by dominated
convergence. Unitarity and density extend it to arbitrary L² vectors. Mathlib's
dense-subset/uniform-Lipschitz theorem also gives joint continuity.

The project retains a full internal derivation in
`formal/notes/DS2-analytic-proof-notes-2026-10-31.md`. This alternative establishes
ambient strong continuity, but does not itself certify the original choice of
dense class or authorize carrying proof-correspondence evidence to it.

## Exact remaining regularity boundary

[WeylBridge](../MathResearch/Spinor/WeylBridge.lean) declares
`WeylRegularityOnBall E`: for a locally integrable E-valued function on B whose
ordinary distributional Laplacian vanishes, there exists an almost-everywhere
equal smooth harmonic representative. E is finite-dimensional over ℝ.

This is an **unproved explicit input**, not an axiom or a supplied instance.
`weakKernel_smoothRepresentative_of_weyl` applies it to the proved weak
harmonicity. `continuousRepresentative_unique` proves uniqueness on B when
continuous representatives exist. No exact outside-source theorem has been
imported or independently verified for this input. A clean axiom audit does
not discharge it.

Remaining DS2 obligations are Weyl regularity itself, the classical/weak
comparison, identification with the independently written compatible-row
model, kernel invariance and the resulting restricted representation, and
the interior harmonic estimates asserted in the written proof. DS3/DS4 retain
their earlier explicit unmet inputs. No new complete wiki target is claimed.

## Replay

Lean 4.35.0 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` are unchanged.
Run `python3 scripts/verify.py --clean-local` for the complete local rebuild
and transitive axiom audit. Run
`bash scripts/lake.sh env lean -DwarningAsError=true docs/DS2-analytic-statement-check.lean`
for the exact signatures, definitions and remaining input. Historical proof
files and evidence remain intact. This is an author self-check, not independent
mathematical review or wiki publication.
