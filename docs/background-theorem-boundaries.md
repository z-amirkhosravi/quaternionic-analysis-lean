# Background theorem boundaries: bounded Lean audit

The researcher's requirement is to verify the written research argument, with
its named theorem referrals. Proving the same conclusion by a substituted
argument is insufficient. A missing background theorem stays an explicit
hypothesis; its proof belongs to a separate development and exposition.

The [exposition inventory](standard-theorems.md) lists the
standard results, their exact formal scope, source declarations and status.
The current DS3–DS4 worktree is based on the fixed DS2 delivery
`ca7249436a64e8c045bdbeb15e6aac992cc0d064`. This audit inspects the major analytic
DS2 dependencies, current DS3–DS4, EI7's quaternionic SO(4) construction, and
TH1's Mellin/Gamma interface. It is not a retrospective proof-correspondence
review of every earlier theorem.

## Findings

**Weyl regularity.** The project did prove Weyl's lemma locally, but its proof
is already separate: `Analysis/Weyl*.lean` and the named theorem
`Spinor.weylRegularityOnBall`. `weakKernel_smoothRepresentative` invokes that
named theorem through the previously explicit Weyl interface. The research
application does not contain the regularized Newton-potential proof. The new
expository article should expose this independent standard result, with unit
ball scope. Its verification does not certify a particular published proof of
Weyl's lemma; the supplied proof is the one in the retained internal notes.

**Interior estimates.** `Analysis/HarmonicPartials.lean` proves the harmonic
derivative test formula. `Spinor/InteriorEvaluation.lean` applies it to the
weighted regular Hilbert space and invokes mathlib's Bochner integral theorem.
These named declarations supply the DS2 estimates and later compact averaging.
No extraction from the assembled DS2 theorem is needed. A separate article
must state the actual domain, derivative and integrability hypotheses.

**Compact-support density.** The adapted Urysohn/simple-function proof is in
`Spinor/CompactDensity.lean`; the application in `CompactContinuity.lean` calls
`dense_compactContinuousBallClasses`. The density theorem deserves its own
expository statement. The concrete action's continuity calculation remains
part of DS2's written argument. The earlier bounded-continuous alternative
remains historical and is excluded from the canonical DS2 proof route.

**Compact polynomial irreducibility and Schur orthogonality.** The new proofs
are in independent `CompactIrreducible.lean` and `CompactSchur.lean` modules.
DS3/DS4 invoke their named declarations. Only positive-degree quaternionic
polynomial representations are proved here; general SU(2)/compact-group
statements must not receive broader verification labels. Elementary invariant
span and transport lemmas were also moved out of the research assembly into
`Analysis/UnitaryIrreducible.lean`.

**Spherical/radial mean values and quotient Haar integration.** These have not
been proved. Their precise statements are explicit parameters of DS3/DS4.
No replacement derivations are inserted into the research argument, no global
axioms are added, and no full-verification label is justified. Existence of
the normalized Haar measure satisfying the quotient formula also remains open
in this formal development. An axiom audit alone would not disclose these
hypotheses, so the statement check prints them separately.

**EI7's quaternionic SO(4) input.** The surjectivity/kernel proof already lives
in `Fueter/QuaternionRotations.lean`; the research action calls the named
results. Mathlib supplies Cartan–Dieudonné. The separate article should not
confuse the proved algebraic assertions with an unproved topological-covering
assertion. This result was added to the inventory after inspecting the earlier
proofs.

**Polynomial unitarity.** The standard norm law was already proved separately
in `Spinor/PolynomialUnitary.lean`. It was added to the inventory, naturally
alongside the compact irreducibility article.

**TH1's Gamma/Mellin input.** The Gamma identity is a specialization of a named
mathlib theorem, and interchange uses mathlib's integration machinery. These
standard proofs have not been reinvented inside TH1. The local real-series
lemmas have their own `RealMellin.lean` module.

## Consequences for evidence and exposition

Earlier source releases and evidence are retained unchanged. No prior DS2
claim needs downgrading solely because its transitive axiom audit sees the
proof of a named standard theorem. That is normal dependency checking and
is distinct from inserting that proof into the written research argument.
The earlier description “expanded Weyl/interior/density arguments” should be
read as **separate verified background results plus their research uses**;
the exposition should make these referrals visible.

This audit found no embedded reproof requiring removal from the inspected
DS2/EI7/TH1 research declarations. It did extract the new generic DS3/DS4 helper
proofs into a supporting module. It does not conclude that every earlier
written argument has been checked for correspondence. Future audits must keep
that distinction and report any additional mismatch specifically.

The current DS3–DS4 correspondence note records the exact written steps and
unverified premises. Research and background results receive distinct status
entries in the milestone evidence. The Expositor owns any subsequent articles;
the Lean agent changes no wiki text and introduces no visitor approval gate.
