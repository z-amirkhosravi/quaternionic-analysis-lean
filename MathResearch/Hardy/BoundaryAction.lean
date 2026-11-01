module
public import MathResearch.Hardy.Fiber
public import MathResearch.Hardy.BoundaryGeometry

/-! The pointwise spinor principal-series formula and its exact multiplier. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
namespace MathResearch.Hardy
open Spinor

def boundaryPull (g : Sp11) (f : Sphere → Fiber) (q : Sphere) : Fiber :=
  (Quaternion.normSq (mobiusDenominator g q))⁻¹ •
    polynomialRepresentation 1 (quaternionMatrix ((mobiusDenominator g q)⁻¹))
      (f (sphereAction g q))

def boundaryAction (g : Sp11) := boundaryPull g⁻¹

@[simp] theorem boundaryPull_one (f : Sphere → Fiber) : boundaryPull 1 f = f := by
  funext q
  simp [boundaryPull]

theorem boundaryPull_mul (g h : Sp11) (f : Sphere → Fiber) :
    boundaryPull (g*h) f = boundaryPull h (boundaryPull g f) := by
  funext q
  have hJ := denominator_ne_zero_closed h (q := (q:ℍ)) (by rw [Fueter.unitQuaternion_norm])
  simp only [boundaryPull,Sp11.coe_mul,sphereAction_mul,
    mobiusDenominator_cocycle g h hJ,sphereAction_val,map_mul,mul_inv_rev,
    quaternionMatrix_mul,Module.End.mul_apply,LinearMap.map_smul_of_tower,smul_smul]

@[simp] theorem boundaryAction_one (f : Sphere → Fiber) : boundaryAction 1 f = f := by
  simp [boundaryAction]

theorem boundaryAction_mul (g h : Sp11) (f : Sphere → Fiber) :
    boundaryAction (g*h) f = boundaryAction g (boundaryAction h f) := by
  simp only [boundaryAction,mul_inv_rev,boundaryPull_mul]

theorem boundaryPull_norm (g : Sp11) (f : Sphere → Fiber) (q : Sphere) :
    ‖boundaryPull g f q‖ = ‖mobiusDenominator g q‖⁻¹ ^ 3 * ‖f (sphereAction g q)‖ := by
  simp only [boundaryPull,norm_smul,quaternionAction_norm,pow_one,norm_inv,
    Quaternion.normSq_eq_norm_mul_self,Real.norm_eq_abs,mul_inv_rev]
  rw [abs_of_nonneg (by positivity : 0 ≤ ‖mobiusDenominator g q‖⁻¹ * ‖mobiusDenominator g q‖⁻¹)]
  ring

theorem boundaryPull_norm_sq (g : Sp11) (f : Sphere → Fiber) (q : Sphere) :
    ‖boundaryPull g f q‖^2 = boundaryJacobian g q * ‖f (sphereAction g q)‖^2 := by
  rw [boundaryPull_norm]
  simp only [boundaryJacobian,Quaternion.normSq_eq_norm_mul_self,mul_pow,mul_inv_rev]
  ring

theorem boundaryPull_add (g : Sp11) (f h : Sphere → Fiber) :
    boundaryPull g (f+h) = boundaryPull g f + boundaryPull g h := by
  funext q
  simp only [boundaryPull,Pi.add_apply,map_add,smul_add]

theorem boundaryPull_smul (g : Sp11) (z : ℂ) (f : Sphere → Fiber) :
    boundaryPull g (z • f) = z • boundaryPull g f := by
  funext q
  simp only [boundaryPull,Pi.smul_apply,map_smul]
  exact smul_comm _ _ _

theorem toQuaternion_boundaryAction (g : Sp11) (f : Sphere → Fiber) (q : Sphere) :
    toQuaternion (boundaryAction g f q) =
      (Quaternion.normSq (mobiusDenominator (g⁻¹ : Sp11) q))⁻¹ •
        ((mobiusDenominator (g⁻¹ : Sp11) q)⁻¹ * toQuaternion (f (sphereAction g⁻¹ q))) := by
  rw [boundaryAction,boundaryPull,toQuaternion_real_smul,toQuaternion_action]

end MathResearch.Hardy
