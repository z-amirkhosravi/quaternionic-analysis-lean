# SC1–SC2 canonical proof correspondence repair

This cumulative delivery repairs review findings PC-01 and PC-02 against the
unchanged canonical `research/R060/liu-zhang-step.md` at accepted revision
`f0fd277cbac86db644f24fddff73ec6e78417e8f`. It is based on standalone release
`84b66cce3de6e5d9fee23838cb8657aae21592c3`; the separate Hardy branch is excluded.
The exact full written statement and proof, SHA-256, and review fingerprint
are retained in `SC1-SC2-correspondence-proof-source.json`.

## PC-01: L4 and Maurer–Cartan imply L6

`ballCurvature_eq` now invokes the separately proved
`MathResearch.Analysis.maurerCartan` for the actual section and inverse.
`ballSections_contDiffAt_two` and `ballSection_inverse` discharge its
hypotheses. The existing `ballSection_maurerCartan` gives L4 throughout the
ball. The chain rule for the lower-right continuous linear entry map and
local equality of derivatives identify dA. Taking the lower-right product
block gives s⁻² bar(v)w+A(v)A(w). The resulting equation is precisely L6.

The new background statement and its complete mathematical proof are in
[MaurerCartan-proof.md](MaurerCartan-proof.md), ready for separate exposition.
This is a genuine inference from Maurer–Cartan, not a wrapper around the old
curvature computation. `fderiv_ballConnection` remains available with its old
statement and proof, but is absent from the repaired target's dependencies.

## PC-02: L9 implies L11

The repaired `projected_connection_homogeneous` follows the displayed written
inference with n=m+1:

1. `connectionCoefficient_eq_inner` identifies C_v=bar(v)q−⟨v,q⟩.
2. `infinitesimal_quaternion_sub` splits the action linearly.
3. The existing `infinitesimal_real` gives dτ_n(r)p=nrp for a real scalar r.
4. Differentiation and the column action commute with this scalar subtraction.
5. `coordinateBasis_inner_sum` proves Σ_v⟨v,q⟩v=q; `matrixColumn_inner_sum`
   transports it to the quaternion column action.
6. The existing `projected_full_homogeneous` is L9. Subtracting the scalar sum
   gives 2(n+1)qT_np−nqT_np=(n+2)qT_np, exactly L11.

The previous arbitrary-polynomial `projected_connection_identity` is retained
as a separate proved helper. It is absent from the repaired homogeneous
identity and SC2's dependencies. The first/full projected identity and its
homogeneity proof are unchanged. Target types, degrees, conventions and
version labels are unchanged.

## Files, assumptions, and evidence

Only two existing mathematical files change:
`MathResearch/Spinor/BallConnection.lean` and
`MathResearch/Spinor/ProjectedConnection.lean`. One independent background
file is added: `MathResearch/Analysis/MaurerCartan.lean`. All earlier background
modules, other mathematical files, root imports, and pinned environment/checker
files are preserved byte-for-byte. The preservation record names every file
and compares each against the base Git blob.

There are no unverified mathematical premises added to SC1 or SC2. The
background regularity and inverse hypotheses are explicitly proved in the
application. Kernel audits separately report foundational axioms; they are not
being used as evidence of written-proof correspondence. The new route check
traverses actual proof constants and requires the named inferences while
forbidding the two superseded direct-calculation helpers. This is an author
self-check, not an independent review.

Research/wiki prose, existing delivery pins, the accepted/preparation trees,
and the Hardy delivery are unchanged. The original SC1/SC3 ambient smoothness
scope, the specified 1/24 normalization, and all other review qualifications
remain in effect. No publication or integration is performed by this delivery.
