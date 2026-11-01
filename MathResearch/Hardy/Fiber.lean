module
public import MathResearch.Spinor.RowAction

/-! The endpoint fibre is ordinary quaternions with right complex scalars.
We retain the existing degree-one polynomial Hilbert model and prove its exact
identification with a-jb, including norm, scalars and left multiplication. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators
namespace MathResearch.Hardy
open Spinor

abbrev Fiber := BinaryForm 1

def toQuaternion (p : Fiber) : ℍ := pack (coefficients 1 p 0) (coefficients 1 p 1)

theorem toQuaternion_injective : Function.Injective toQuaternion := by
  intro p q h
  have H : (coefficients 1 p 0,coefficients 1 p 1) =
      (coefficients 1 q 0,coefficients 1 q 1) := pack_injective h
  apply coefficients_injective 1
  funext i
  fin_cases i
  · exact congrArg Prod.fst H
  · exact congrArg Prod.snd H

theorem toQuaternion_surjective : Function.Surjective toQuaternion := by
  intro q
  obtain ⟨⟨a,b⟩, hab⟩ := pack_surjective q
  refine ⟨(coefficientEquiv 1).symm ![a,b], ?_⟩
  have hc : coefficients 1 ((coefficientEquiv 1).symm ![a,b]) = ![a,b] :=
    (coefficientEquiv 1).apply_symm_apply _
  simpa only [toQuaternion,hc,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using hab

def quaternionEquiv : Fiber ≃ ℍ := Equiv.ofBijective toQuaternion
  ⟨toQuaternion_injective,toQuaternion_surjective⟩

@[simp] theorem toQuaternion_zero : toQuaternion 0 = 0 := by simp [toQuaternion,pack]
@[simp] theorem toQuaternion_add (p q : Fiber) :
    toQuaternion (p+q) = toQuaternion p + toQuaternion q := by
  simp only [toQuaternion,map_add,Pi.add_apply,pack_add]

theorem toQuaternion_smul (z : ℂ) (p : Fiber) :
    toQuaternion (z • p) = toQuaternion p * (z:ℍ) := by
  simp only [toQuaternion,map_smul,Pi.smul_apply,smul_eq_mul,pack_smul]

theorem toQuaternion_real_smul (r : ℝ) (p : Fiber) :
    toQuaternion (r • p) = r • toQuaternion p := by
  change toQuaternion ((r:ℂ) • p) = _
  simp only [toQuaternion,map_smul,Pi.smul_apply,smul_eq_mul,pack_real_smul]

@[simp] theorem norm_toQuaternion (p : Fiber) : ‖toQuaternion p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [toQuaternion,pack_norm_sq,binaryForm_norm_sq,Fin.sum_univ_two]

theorem toQuaternion_eq_fueter (p : Fiber) : toQuaternion p = fueterCoefficients 0 p 0 := by
  change _ = pack (coefficients 0 (derivative 0 0 p) 0) (coefficients 0 (derivative 0 1 p) 0)
  rw [coefficient_derivative_X,coefficient_derivative_Y]
  simp [toQuaternion]

theorem degreeZero_action (M : Matrix2) (p : BinaryForm 0) :
    polynomialRepresentation 0 M p = p := by
  have hp := monomialForm_expansion 0 p
  rw [Fin.sum_univ_one] at hp
  rw [← hp,map_smul]
  congr 1
  apply Subtype.ext
  simp [polynomialRepresentation,monomialForm,exponent,polynomialAction]

/-- The polynomial action at degree one is literally left quaternion multiplication. -/
theorem toQuaternion_action (a : ℍ) (p : Fiber) :
    toQuaternion (polynomialRepresentation 1 (quaternionMatrix a) p) = a * toQuaternion p := by
  rw [toQuaternion_eq_fueter,fueterCoefficients_action]
  congr 1
  simp only [rowSubstitution,coefficientActionMatrix,Matrix.transpose_apply,
    degreeZero_action]
  change (∑ x : Fin 1, fueterCoefficients 0 p x *
    ((coefficients 0 (monomialForm 0 x) 0 : ℂ) : ℍ)) = _
  rw [Fin.sum_univ_one]
  have hc : coefficients 0 (monomialForm 0 0) 0 = 1 := by
    simp [monomialForm,coefficients,exponent]
  rw [hc,Quaternion.coeComplex_one,mul_one,← toQuaternion_eq_fueter]

/-- H1's multiplier in the ordinary quaternion convention. -/
theorem toQuaternion_ballAction (g : QuaternionMatrix2) (f : ℍ → Fiber) (q : ℍ) :
    toQuaternion (ballAction 1 g f q) =
      (Quaternion.normSq (mobiusDenominator g q))⁻¹ •
        ((mobiusDenominator g q)⁻¹ * toQuaternion (f (mobiusPoint g q))) := by
  rw [ballAction,toQuaternion_real_smul,toQuaternion_action]

end MathResearch.Hardy
