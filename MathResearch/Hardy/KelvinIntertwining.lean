module
public import MathResearch.Hardy.BlockSwap
public import MathResearch.Hardy.Space

/-! The exact W-conjugation identity in the boundary Hilbert space. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace MathResearch.Hardy
open Spinor

theorem kelvinL2_intertwining (area : BoundaryAreaFormula) (g : Sp11) (f : BoundaryL2) :
    kelvinUnitary (boundaryRepresentation area g (kelvinUnitary f)) =
      boundaryRepresentation area (blockSwap g) f := by
  apply Lp.ext
  have hi := (Measure.measurePreserving_inv unitQuaternionHaar).quasiMeasurePreserving
  have h2 := hi.ae (boundaryL2Action_ae area g (kelvinL2 f))
  have h3 := hi.ae ((sphere_quasiMeasurePreserving area g⁻¹).ae (kelvinL2_ae f))
  filter_upwards [kelvinL2_ae (boundaryL2Action area g (kelvinL2 f)),h2,h3,
    boundaryL2Action_ae area (blockSwap g) f] with q h1 h2 h3 h4
  change kelvinL2 (boundaryL2Action area g (kelvinL2 f)) q = boundaryL2Action area (blockSwap g) f q
  rw [h1,h4,← congrFun (kelvin_boundaryAction g f) q]
  change polynomialRepresentation 1 (quaternionMatrix (q⁻¹:Sphere))
    (boundaryL2Action area g (kelvinL2 f) q⁻¹) = _
  rw [h2]
  simp only [kelvin,boundaryAction,boundaryPull] at h3 ⊢
  rw [h3]

@[simp] theorem kelvinUnitary_apply_apply (f : BoundaryL2) : kelvinUnitary (kelvinUnitary f) = f :=
  kelvinL2_involution f

def negativeHardyBoundary : Submodule ℂ BoundaryL2 :=
  hardyBoundary.map kelvinUnitary.toLinearEquiv.toLinearMap

theorem negativeHardyBoundary_invariant (area : BoundaryAreaFormula)
    (hinv : UnitaryInvariant (boundaryRepresentation area) hardyBoundary) :
    UnitaryInvariant (boundaryRepresentation area) negativeHardyBoundary := by
  intro g f hf
  obtain ⟨v,hv,rfl⟩ := hf
  refine ⟨boundaryRepresentation area (blockSwap g) v,hinv _ _ hv,?_⟩
  have h := kelvinL2_intertwining area (blockSwap g) (kelvinUnitary v)
  change kelvinUnitary (boundaryRepresentation area (blockSwap g) v) =
    boundaryRepresentation area g (kelvinUnitary v)
  simpa only [kelvinUnitary_apply_apply,blockSwap_involution] using h

end MathResearch.Hardy
