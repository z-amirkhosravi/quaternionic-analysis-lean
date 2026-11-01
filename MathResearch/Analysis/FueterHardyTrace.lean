module
public import MathResearch.Hardy.Representation

/-! OPEN analytic interfaces for the n=1 Hardy realization.

The internal proof refers to orthogonal homogeneous harmonic expansion and
Parseval. They must supply radial traces, reconstruction and bounded point
evaluations on the closed space of regular polynomial traces. This file states
those precise outputs, but does NOT prove the expansion theorem. Invariance
and compatibility of traces with C7 are also still open local bridges, not
consequences of a reference to representation classification.

No instance or axiom asserts these inputs. Every consumer must display them.
The compact-average/irreducibility argument is proved in Hardy/Irreducible,
using the already proved spherical mean-value theorem. -/
@[expose] public section
noncomputable section
open scoped Quaternion ContDiff
open InnerProductSpace
namespace MathResearch.Hardy
open Spinor

/-- Outputs required from the written homogeneous-expansion/trace argument.
`evaluation_ext` concerns functions on B, without imposing values outside B.
The action formula is an additional local trace-equivariance obligation. -/
structure HardyTraceData (area : BoundaryAreaFormula) (hinv : HardyInvariant area) where
  evaluation : ∀ q : ℍ, q ∈ Ball → HardyBoundary →L[ℂ] Fiber
  evaluation_ext : ∀ f h : HardyBoundary,
    (∀ q (hq : q ∈ Ball), evaluation q hq f = evaluation q hq h) → f = h
  representative : ∀ f : HardyBoundary, ∃ F : ℍ → Fiber,
    IsHardy F ∧ HarmonicOnNhd F Ball ∧
    (∀ q (hq : q ∈ Ball), evaluation q hq f = F q) ∧
    IsBoundaryTrace F f.val ∧ hardyNormSq F = ‖f‖^2
  realization : ∀ F : ℍ → Fiber, IsHardy F → ∃ f : HardyBoundary,
    (∀ q (hq : q ∈ Ball), evaluation q hq f = F q) ∧
    IsBoundaryTrace F f.val ∧ hardyNormSq F = ‖f‖^2
  constant_value : ∀ q (hq : q ∈ Ball) v, evaluation q hq (constantHardy v) = v
  action_value : ∀ (g : Sp11) (f : HardyBoundary) (F : ℍ → Fiber),
    IsRegular F → (∀ q (hq : q ∈ Ball), evaluation q hq f = F q) →
    ∀ q (hq : q ∈ Ball), evaluation q hq (hardyRepresentation area hinv g f) =
      ballRepresentation 1 g F q

end MathResearch.Hardy
