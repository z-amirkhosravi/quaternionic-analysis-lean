module
public import MathResearch.Hardy.BoundaryAction
public import MathResearch.Analysis.BoundaryAreaFormula

/-! Descent of the explicit boundary formula to genuine Haar L².
Only the named geometric change-of-variables theorem is an input. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ENNReal
open MeasureTheory
namespace MathResearch.Hardy
open Spinor
abbrev BoundaryL2 := Lp Fiber 2 unitQuaternionHaar

theorem boundaryPull_aestronglyMeasurable (area : BoundaryAreaFormula) (g : Sp11)
    {f : Sphere → Fiber} (hf : AEStronglyMeasurable f unitQuaternionHaar) :
    AEStronglyMeasurable (boundaryPull g f) unitQuaternionHaar := by
  have hc := hf.comp_quasiMeasurePreserving (sphere_quasiMeasurePreserving area g)
  have hJ : Measurable (fun q : Sphere => mobiusDenominator g q) :=
    (measurable_mobiusDenominator g).comp measurable_subtype_coe
  have hp := (contDiff_quaternionPolynomialRepresentation 1).continuous.comp_aestronglyMeasurable
    (hJ.inv.aestronglyMeasurable.prodMk hc)
  exact (Quaternion.continuous_normSq.measurable.comp hJ).inv.aestronglyMeasurable.smul hp

theorem boundaryPull_memLp (area : BoundaryAreaFormula) (g : Sp11)
    {f : Sphere → Fiber} (hf : MemLp f 2 unitQuaternionHaar) :
    MemLp (boundaryPull g f) 2 unitQuaternionHaar := by
  apply (memLp_two_iff_integrable_sq_norm
    (boundaryPull_aestronglyMeasurable area g hf.aestronglyMeasurable)).mpr
  simp_rw [boundaryPull_norm_sq]
  exact (boundary_integrable_change area g (fun q => ‖f q‖^2)).mp
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)

def boundaryL2Action (area : BoundaryAreaFormula) (g : Sp11) (f : BoundaryL2) : BoundaryL2 :=
  (boundaryPull_memLp area g⁻¹ (Lp.memLp f)).toLp (boundaryAction g f)

theorem boundaryL2Action_ae (area : BoundaryAreaFormula) (g : Sp11) (f : BoundaryL2) :
    (boundaryL2Action area g f : Sphere → Fiber) =ᵐ[unitQuaternionHaar] boundaryAction g f :=
  MemLp.coeFn_toLp _

theorem boundaryL2Action_norm (area : BoundaryAreaFormula) (g : Sp11) (f : BoundaryL2) :
    ‖boundaryL2Action area g f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq_integral,l2_norm_sq_integral]
  calc
    _ = ∫ q, ‖boundaryAction g f q‖^2 ∂unitQuaternionHaar :=
      integral_congr_ae ((boundaryL2Action_ae area g f).mono fun _ h => congrArg (fun p => ‖p‖^2) h)
    _ = _ := by
      simp only [boundaryAction,boundaryPull_norm_sq]
      exact boundary_integral_change area g⁻¹ (fun q => ‖f q‖^2)

theorem boundaryL2Action_add (area : BoundaryAreaFormula) (g : Sp11) (f h : BoundaryL2) :
    boundaryL2Action area g (f+h) = boundaryL2Action area g f + boundaryL2Action area g h := by
  apply Lp.ext
  have ha := (sphere_quasiMeasurePreserving area g⁻¹).ae (Lp.coeFn_add f h)
  filter_upwards [boundaryL2Action_ae area g (f+h),boundaryL2Action_ae area g f,
    boundaryL2Action_ae area g h,Lp.coeFn_add (boundaryL2Action area g f)
      (boundaryL2Action area g h),ha] with q h1 h2 h3 h4 h5
  rw [h1,h4]
  simp only [Pi.add_apply] at h5 ⊢
  rw [h2,h3]
  simp only [boundaryAction,boundaryPull,h5,map_add,smul_add]

theorem boundaryL2Action_smul (area : BoundaryAreaFormula) (g : Sp11) (z : ℂ) (f : BoundaryL2) :
    boundaryL2Action area g (z • f) = z • boundaryL2Action area g f := by
  apply Lp.ext
  have ha := (sphere_quasiMeasurePreserving area g⁻¹).ae (Lp.coeFn_smul z f)
  filter_upwards [boundaryL2Action_ae area g (z • f),boundaryL2Action_ae area g f,
    Lp.coeFn_smul z (boundaryL2Action area g f),ha] with q h1 h2 h3 h4
  rw [h1,h3]
  simp only [Pi.smul_apply] at h4 ⊢
  rw [h2]
  simp only [boundaryAction,boundaryPull,h4,map_smul]
  exact smul_comm _ _ _

@[simp] theorem boundaryL2Action_one (area : BoundaryAreaFormula) (f : BoundaryL2) :
    boundaryL2Action area 1 f = f := by
  apply Lp.ext
  simpa only [boundaryAction_one] using boundaryL2Action_ae area 1 f

theorem boundaryL2Action_mul (area : BoundaryAreaFormula) (g h : Sp11) (f : BoundaryL2) :
    boundaryL2Action area (g*h) f = boundaryL2Action area g (boundaryL2Action area h f) := by
  apply Lp.ext
  have ha := (sphere_quasiMeasurePreserving area g⁻¹).ae (boundaryL2Action_ae area h f)
  filter_upwards [boundaryL2Action_ae area (g*h) f,
    boundaryL2Action_ae area g (boundaryL2Action area h f),ha] with q h1 h2 h3
  rw [h1,h2,boundaryAction_mul]
  simp only [boundaryAction,boundaryPull] at h3 ⊢
  rw [h3]

def boundaryUnitary (area : BoundaryAreaFormula) (g : Sp11) : BoundaryL2 ≃ₗᵢ[ℂ] BoundaryL2 where
  toFun := boundaryL2Action area g
  invFun := boundaryL2Action area g⁻¹
  map_add' := boundaryL2Action_add area g
  map_smul' := boundaryL2Action_smul area g
  left_inv f := by rw [← boundaryL2Action_mul,inv_mul_cancel,boundaryL2Action_one]
  right_inv f := by rw [← boundaryL2Action_mul,mul_inv_cancel,boundaryL2Action_one]
  norm_map' := boundaryL2Action_norm area g

def boundaryRepresentation (area : BoundaryAreaFormula) : Sp11 →* (BoundaryL2 ≃ₗᵢ[ℂ] BoundaryL2) where
  toFun := boundaryUnitary area
  map_one' := by ext f : 1; exact boundaryL2Action_one area f
  map_mul' g h := by ext f : 1; exact boundaryL2Action_mul area g h f

/-- The actual H1 formula, as an a.e. statement for the L² representation. -/
theorem boundaryRepresentation_formula (area : BoundaryAreaFormula) (g : Sp11) (f : BoundaryL2) :
    (fun q => toQuaternion (boundaryRepresentation area g f q)) =ᵐ[unitQuaternionHaar]
      (fun q => (Quaternion.normSq (mobiusDenominator (g⁻¹ : Sp11) q))⁻¹ •
        ((mobiusDenominator (g⁻¹ : Sp11) q)⁻¹ * toQuaternion (f (sphereAction g⁻¹ q)))) := by
  filter_upwards [boundaryL2Action_ae area g f] with q h
  rw [show boundaryRepresentation area g f q = boundaryL2Action area g f q from rfl,
    h,toQuaternion_boundaryAction]

end MathResearch.Hardy
