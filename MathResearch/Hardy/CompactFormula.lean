module
public import MathResearch.Hardy.BoundaryAction

/-! The exact compact action and its diagonal-M fibre at the point 1. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
namespace MathResearch.Hardy
open Spinor

theorem sphereAction_inverse_compact (a b q : Sphere) :
    sphereAction (compactSp11 (a,b))⁻¹ q = a⁻¹*q*b := by
  have hb : (star (b:ℍ))⁻¹ = b := inv_eq_of_mul_eq_one_left (Unitary.coe_mul_star_self b)
  apply Subtype.ext
  simp [sphereAction_val,Sp11.coe_inv,compactSp11,signatureAdjoint,compactMatrix,mobiusPoint,
    mobiusDenominator,hb,mul_assoc]

theorem boundaryAction_compact (a b : Sphere) (f : Sphere → Fiber) (q : Sphere) :
    boundaryAction (compactSp11 (a,b)) f q =
      polynomialRepresentation 1 (quaternionMatrix b) (f (a⁻¹*q*b)) := by
  have hb : (star (b:ℍ))⁻¹ = b := inv_eq_of_mul_eq_one_left (Unitary.coe_mul_star_self b)
  simp only [boundaryAction,boundaryPull,sphereAction_inverse_compact]
  simp [Sp11.coe_inv,compactSp11,signatureAdjoint,compactMatrix,mobiusDenominator,hb,
    Quaternion.normSq_star,Fueter.unitQuaternion_normSq]

theorem diagonal_fiber_at_one (a : Sphere) (f : Sphere → Fiber) :
    toQuaternion (boundaryAction (compactSp11 (a,a)) f 1) = (a:ℍ) * toQuaternion (f 1) := by
  rw [boundaryAction_compact,mul_one,inv_mul_cancel,toQuaternion_action]

end MathResearch.Hardy
