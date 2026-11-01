module
public import MathResearch.Hardy.BoundaryL2

/-! Kelvin's boundary involution. Haar inversion invariance is already proved;
this construction does not assume the boundary area formula. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion
open MeasureTheory
namespace MathResearch.Hardy
open Spinor

def kelvin (f : Sphere → Fiber) (q : Sphere) : Fiber :=
  polynomialRepresentation 1 (quaternionMatrix (q⁻¹ : Sphere)) (f q⁻¹)

theorem kelvin_formula (f : Sphere → Fiber) (q : Sphere) :
    toQuaternion (kelvin f q) = star (q:ℍ) * toQuaternion (f q⁻¹) :=
  toQuaternion_action _ _

theorem kelvin_involution (f : Sphere → Fiber) : kelvin (kelvin f) = f := by
  funext q
  apply toQuaternion_injective
  simp only [kelvin_formula, inv_inv, Fueter.unitQuaternion_coe_inv, star_star]
  rw [← mul_assoc]
  have h : star (q:ℍ) * (q:ℍ) = 1 := Unitary.coe_star_mul_self q
  rw [h,one_mul]

theorem kelvin_norm (f : Sphere → Fiber) (q : Sphere) : ‖kelvin f q‖ = ‖f q⁻¹‖ := by
  simp [kelvin,quaternionAction_norm]

theorem kelvin_aestronglyMeasurable {f : Sphere → Fiber}
    (hf : AEStronglyMeasurable f unitQuaternionHaar) :
    AEStronglyMeasurable (kelvin f) unitQuaternionHaar := by
  have hc : AEStronglyMeasurable (fun q : Sphere => f q⁻¹) unitQuaternionHaar := hf.comp_quasiMeasurePreserving
    (Measure.measurePreserving_inv unitQuaternionHaar).quasiMeasurePreserving
  have hq : Continuous (fun q : Sphere => (q⁻¹ : Sphere).val) :=
    continuous_subtype_val.comp continuous_inv
  simpa only [kelvin,Function.comp_def] using!
    (contDiff_quaternionPolynomialRepresentation 1).continuous.comp_aestronglyMeasurable
      (hq.aestronglyMeasurable.prodMk hc)

theorem kelvin_memLp {f : Sphere → Fiber} (hf : MemLp f 2 unitQuaternionHaar) :
    MemLp (kelvin f) 2 unitQuaternionHaar := by
  apply (memLp_two_iff_integrable_sq_norm (kelvin_aestronglyMeasurable hf.aestronglyMeasurable)).mpr
  simp_rw [kelvin_norm]
  have h : Integrable (fun q : Sphere => ‖f q‖^2) unitQuaternionHaar :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  simpa only [Function.comp_def] using
    (Measure.measurePreserving_inv unitQuaternionHaar).integrable_comp_of_integrable
      (g := fun q : Sphere => ‖f q‖^2) h

def kelvinL2 (f : BoundaryL2) : BoundaryL2 := (kelvin_memLp (Lp.memLp f)).toLp (kelvin f)

theorem kelvinL2_ae (f : BoundaryL2) :
    (kelvinL2 f : Sphere → Fiber) =ᵐ[unitQuaternionHaar] kelvin f := MemLp.coeFn_toLp _

theorem kelvinL2_involution (f : BoundaryL2) : kelvinL2 (kelvinL2 f) = f := by
  apply Lp.ext
  have ha := (Measure.measurePreserving_inv unitQuaternionHaar).quasiMeasurePreserving.ae (kelvinL2_ae f)
  filter_upwards [kelvinL2_ae (kelvinL2 f),ha] with q h1 h2
  rw [h1]
  change polynomialRepresentation 1 (quaternionMatrix (q⁻¹ : Sphere)) ((kelvinL2 f) q⁻¹) = f q
  rw [h2]
  exact congrFun (kelvin_involution f) q

theorem kelvinL2_norm (f : BoundaryL2) : ‖kelvinL2 f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq_integral,l2_norm_sq_integral]
  calc
    _ = ∫ q, ‖kelvin f q‖^2 ∂unitQuaternionHaar :=
      integral_congr_ae ((kelvinL2_ae f).mono fun _ h => congrArg (fun p => ‖p‖^2) h)
    _ = _ := by simp_rw [kelvin_norm]; exact integral_inv_eq_self (fun q => ‖f q‖^2) unitQuaternionHaar

theorem kelvinL2_add (f h : BoundaryL2) : kelvinL2 (f+h) = kelvinL2 f + kelvinL2 h := by
  apply Lp.ext
  have ha := (Measure.measurePreserving_inv unitQuaternionHaar).quasiMeasurePreserving.ae (Lp.coeFn_add f h)
  filter_upwards [kelvinL2_ae (f+h),kelvinL2_ae f,kelvinL2_ae h,
    Lp.coeFn_add (kelvinL2 f) (kelvinL2 h),ha] with q h1 h2 h3 h4 h5
  rw [h1,h4]
  simp only [Pi.add_apply] at h5 ⊢
  rw [h2,h3]
  simp only [kelvin,h5,map_add]

theorem kelvinL2_smul (z : ℂ) (f : BoundaryL2) : kelvinL2 (z • f) = z • kelvinL2 f := by
  apply Lp.ext
  have ha := (Measure.measurePreserving_inv unitQuaternionHaar).quasiMeasurePreserving.ae (Lp.coeFn_smul z f)
  filter_upwards [kelvinL2_ae (z • f),kelvinL2_ae f,Lp.coeFn_smul z (kelvinL2 f),ha] with q h1 h2 h3 h4
  rw [h1,h3]
  simp only [Pi.smul_apply] at h4 ⊢
  rw [h2]
  simp only [kelvin,h4,map_smul]

def kelvinUnitary : BoundaryL2 ≃ₗᵢ[ℂ] BoundaryL2 where
  toFun := kelvinL2
  invFun := kelvinL2
  left_inv := kelvinL2_involution
  right_inv := kelvinL2_involution
  map_add' := kelvinL2_add
  map_smul' := kelvinL2_smul
  norm_map' := kelvinL2_norm

end MathResearch.Hardy
