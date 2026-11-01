module
public import MathResearch.Hardy.BoundaryGeometry

/-! Exact geometric background input for the Hardy boundary model.
The surface area/Jacobian theorem is kept explicit until its independent
formalization; it is not an axiom or an assertion of unitarity. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace MathResearch.Hardy
open Spinor

/-- Möbius surface change of variables on S³ with normalized area, represented
by unit-quaternion Haar probability. The exponent is 6, not the ball exponent 8. -/
def BoundaryAreaFormula : Prop := ∀ g : Sp11,
  Measure.map (sphereAction g)
    (unitQuaternionHaar.withDensity (fun q => ENNReal.ofReal (boundaryJacobian g q))) =
      unitQuaternionHaar

/-- Null sets can be pulled back once the independently stated area theorem is supplied. -/
theorem sphere_quasiMeasurePreserving (area : BoundaryAreaFormula) (g : Sp11) :
    QuasiMeasurePreserving (sphereAction g) unitQuaternionHaar unitQuaternionHaar := by
  have ha : unitQuaternionHaar ≪ unitQuaternionHaar.withDensity
      (fun q => ENNReal.ofReal (boundaryJacobian g q)) :=
    withDensity_absolutelyContinuous'
      (continuous_boundaryJacobian g).measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun q => ENNReal.ofReal_ne_zero_iff.mpr (boundaryJacobian_pos g q))
  refine ⟨(continuous_sphereAction g).measurable, ?_⟩
  simpa only [area g] using ha.map (continuous_sphereAction g).measurable

/-- Integrability clause, indispensable because Bochner integrals are totalized. -/
theorem boundary_integrable_change (area : BoundaryAreaFormula) (g : Sp11) (f : Sphere → ℝ) :
    Integrable f unitQuaternionHaar ↔
      Integrable (fun q => boundaryJacobian g q * f (sphereAction g q)) unitQuaternionHaar := by
  have H := (sphereHomeomorph g).measurableEmbedding.integrable_map_iff
    (μ := unitQuaternionHaar.withDensity (fun q => ENNReal.ofReal (boundaryJacobian g q))) (g := f)
  rw [show (sphereHomeomorph g : Sphere → Sphere) = sphereAction g from rfl,area g] at H
  rw [H]
  rw [integrable_withDensity_iff_integrable_smul'
    (continuous_boundaryJacobian g).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (boundaryJacobian_pos g _).le,smul_eq_mul,Function.comp_apply]

/-- The matching real integral identity. -/
theorem boundary_integral_change (area : BoundaryAreaFormula) (g : Sp11) (f : Sphere → ℝ) :
    (∫ q, boundaryJacobian g q * f (sphereAction g q) ∂unitQuaternionHaar) =
      ∫ q, f q ∂unitQuaternionHaar := by
  have H := (sphereHomeomorph g).measurableEmbedding.integral_map
    (μ := unitQuaternionHaar.withDensity (fun q => ENNReal.ofReal (boundaryJacobian g q))) f
  rw [show (sphereHomeomorph g : Sphere → Sphere) = sphereAction g from rfl,area g] at H
  rw [H]
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_boundaryJacobian g).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (boundaryJacobian_pos g _).le,smul_eq_mul]

end MathResearch.Hardy
