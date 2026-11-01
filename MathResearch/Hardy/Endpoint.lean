module
public import MathResearch.Hardy.Negative
public import MathResearch.Hardy.Splitting
public import MathResearch.Hardy.Normalization
public import MathResearch.Hardy.CompactFormula
public import MathResearch.Hardy.Invariance
public import MathResearch.Analysis.SpinorEndpointClassification

/-! The written endpoint realization, conditional on the explicitly named
analytic, compact spectral, and external classification inputs. All spaces,
actions, scalar conventions and trace norms are concrete. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
namespace MathResearch.Hardy
open Spinor

/-- H3 recognition, invoking the external theorem at exactly the classification
step. `π₁` and its classification are external; no claim about general Fell
limits or discrete-series classification is hidden in a project definition. -/
theorem H3_realization_of_externalClassification
    (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (tr : HardyTraceData area hinv) (kt : SpinorCompactExpansionData area)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π₁ : Sp11 →* (E ≃ₗᵢ[ℂ] E)) (classification : SpinorEndpointClassification area kt π₁) :
    ∃ e : HardyBoundary ≃ₗᵢ[ℂ] E,
      ∀ g f, e (hardyRepresentation area hinv g f) = π₁ g (e f) := by
  apply classification HardyBoundary (hardyRepresentation area hinv) hardyBoundary.subtypeₗᵢ
    (H1_irreducible_of_traceData area hinv tr).1
  · intro g f
    rfl
  · rw [kt.hardy_span]
    exact Submodule.range_subtype hardyBoundary

/-- A combined, explicitly CONDITIONAL milestone. The conclusion includes the
usual finite-radial-norm function realization via the same trace data, both
irreducible summands, their orthogonal Hilbert sum, and the unitary intertwiner
to externally supplied π₁. It does not certify the open input theorems. -/
theorem Hardy_endpoint_realization_of_inputs
    (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (tr : HardyTraceData area hinv) (kt : SpinorCompactExpansionData area)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π₁ : Sp11 →* (E ≃ₗᵢ[ℂ] E)) (classification : SpinorEndpointClassification area kt π₁) :
    TopologicallyIrreducible (hardyRepresentation area hinv) ∧
    TopologicallyIrreducible (negativeRepresentation area hinv) ∧
    (∀ g (f : NegativeHardy), (negativeRepresentation area hinv g f).val =
      boundaryRepresentation area g f.val) ∧
    (∀ f : NegativeHardy, Continuous (fun g : Sp11 => negativeRepresentation area hinv g f)) ∧
    (∀ f : HardyBoundary, Continuous (fun g : Sp11 => hardyRepresentation area hinv g f)) ∧
    hardyBoundary ≤ negativeHardyBoundaryᗮ ∧
    (hardyBoundary ⊔ negativeHardyBoundary).topologicalClosure = ⊤ ∧
    (∀ F : ℍ → Fiber, IsHardy F → ∃ f : HardyBoundary,
      (∀ q (hq : q ∈ Ball), tr.evaluation q hq f = F q) ∧
      IsBoundaryTrace F f.val ∧ hardyNormSq F = ‖f‖^2) ∧
    (∃ e : HardyBoundary ≃ₗᵢ[ℂ] E, ∀ g f, e (hardyRepresentation area hinv g f) = π₁ g (e f)) := by
  have h1 := H1_irreducible_of_traceData area hinv tr
  have h2 := H2_orthogonal_splitting_of_compactExpansion area kt
  exact ⟨h1.1,H2_negative_irreducible_of_traceData area hinv tr,negativeRepresentation_formula area hinv,
    stronglyContinuous_negativeRepresentation area hinv,h1.2.1,h2.1,h2.2,h1.2.2,
    H3_realization_of_externalClassification area hinv tr kt π₁ classification⟩

/-- The endpoint recognition with invariance proved by SC3 and the named
polynomial approximation input, rather than assumed independently. -/
theorem Hardy_pi1_of_background
    (area : BoundaryAreaFormula) (approximation : RegularPolynomialBoundaryApproximation)
    (tr : HardyTraceData area (hardyInvariant_of_polynomialApproximation area approximation))
    (kt : SpinorCompactExpansionData area)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π₁ : Sp11 →* (E ≃ₗᵢ[ℂ] E)) (classification : SpinorEndpointClassification area kt π₁) :
    ∃ e : HardyBoundary ≃ₗᵢ[ℂ] E, ∀ g f,
      e (hardyRepresentation area (hardyInvariant_of_polynomialApproximation area approximation) g f) =
        π₁ g (e f) :=
  H3_realization_of_externalClassification area
    (hardyInvariant_of_polynomialApproximation area approximation) tr kt π₁ classification

end MathResearch.Hardy
