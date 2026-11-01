module
public import MathResearch.Hardy.BoundaryAction
public import Mathlib.Analysis.Complex.Trigonometric

/-! The fixed-point character of the actual a_t in the internal note.
This checks the factor e^(3t/2); it does not substitute for the full induced-
section model or its external classification. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
namespace MathResearch.Hardy
open Spinor

def hyperbolicMatrix (t : ℝ) : QuaternionMatrix2 :=
  !![(Real.cosh (t/2):ℍ),(Real.sinh (t/2):ℍ);(Real.sinh (t/2):ℍ),(Real.cosh (t/2):ℍ)]

theorem hyperbolicMatrix_isSp11 (t : ℝ) : IsSp11 (hyperbolicMatrix t) := by
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    ext <;> simp [hyperbolicMatrix,signatureAdjoint,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals nlinarith [Real.cosh_sq_sub_sinh_sq (t/2)]

def hyperbolicElement (t : ℝ) : Sp11 := ⟨hyperbolicMatrix t,hyperbolicMatrix_isSp11 t⟩

theorem hyperbolicElement_inv (t : ℝ) : (hyperbolicElement t)⁻¹ = hyperbolicElement (-t) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicElement,hyperbolicMatrix,signatureAdjoint,neg_div]

theorem hyperbolic_denominator (t : ℝ) :
    mobiusDenominator (hyperbolicElement t) 1 = (Real.exp (t/2):ℍ) := by
  simp only [hyperbolicElement,hyperbolicMatrix,mobiusDenominator,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_one]
  rw [← Quaternion.coe_add,Real.sinh_add_cosh]

theorem hyperbolic_fixed (t : ℝ) : sphereAction (hyperbolicElement t) 1 = 1 := by
  apply Subtype.ext
  change mobiusPoint (hyperbolicElement t) 1 = 1
  rw [mobiusPoint,hyperbolic_denominator]
  have hnum : (hyperbolicElement t).val 0 0 * 1 + (hyperbolicElement t).val 0 1 =
      (Real.exp (t/2):ℍ) := by
    simp only [hyperbolicElement,hyperbolicMatrix,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_one]
    rw [← Quaternion.coe_add,Real.cosh_add_sinh]
  rw [hnum,mul_inv_cancel₀]
  intro h
  exact Real.exp_ne_zero (t/2) (congrArg (fun q : ℍ => q.re) h)

theorem boundaryAction_hyperbolic_fixed (t : ℝ) (f : Sphere → Fiber) :
    toQuaternion (boundaryAction (hyperbolicElement t) f 1) =
      Real.exp (3*t/2) • toQuaternion (f 1) := by
  rw [toQuaternion_boundaryAction,hyperbolicElement_inv,hyperbolic_fixed]
  change (Quaternion.normSq (mobiusDenominator (hyperbolicElement (-t)) 1))⁻¹ •
    ((mobiusDenominator (hyperbolicElement (-t)) 1)⁻¹ * toQuaternion (f 1)) = _
  rw [hyperbolic_denominator]
  rw [Quaternion.normSq_coe,← Quaternion.coe_inv,Quaternion.coe_mul_eq_smul,smul_smul]
  congr 1
  rw [← Real.exp_nat_mul,← Real.exp_neg,← Real.exp_neg,← Real.exp_add]
  congr 1
  ring

end MathResearch.Hardy
