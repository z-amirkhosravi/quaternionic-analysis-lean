module
public import MathResearch.Hardy.Kelvin

/-! Conjugation by W=[0,1;1,0], which reverses the defining form but
preserves Sp(1,1). -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
namespace MathResearch.Hardy
open Spinor

def swapMatrix (g : QuaternionMatrix2) : QuaternionMatrix2 := !![g 1 1,g 1 0;g 0 1,g 0 0]

@[simp] theorem swapMatrix_one : swapMatrix 1 = 1 := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [swapMatrix]

@[simp] theorem swapMatrix_swap (g : QuaternionMatrix2) : swapMatrix (swapMatrix g) = g := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [swapMatrix]

theorem swapMatrix_mul (g h : QuaternionMatrix2) : swapMatrix (g*h) = swapMatrix g * swapMatrix h := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;>
    simp [swapMatrix,Matrix.mul_apply,Fin.sum_univ_two,add_comm]

theorem swapMatrix_signature (g : QuaternionMatrix2) :
    swapMatrix (signatureAdjoint g) = signatureAdjoint (swapMatrix g) := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [swapMatrix,signatureAdjoint]

def blockSwap : Sp11 ≃* Sp11 where
  toFun g := ⟨swapMatrix g,by
    constructor
    · rw [← swapMatrix_signature,← swapMatrix_mul,g.isSp11.1,swapMatrix_one]
    · rw [← swapMatrix_signature,← swapMatrix_mul,g.isSp11.2,swapMatrix_one]⟩
  invFun g := ⟨swapMatrix g,by
    constructor
    · rw [← swapMatrix_signature,← swapMatrix_mul,g.isSp11.1,swapMatrix_one]
    · rw [← swapMatrix_signature,← swapMatrix_mul,g.isSp11.2,swapMatrix_one]⟩
  left_inv g := Subtype.ext (swapMatrix_swap g)
  right_inv g := Subtype.ext (swapMatrix_swap g)
  map_mul' g h := Subtype.ext (swapMatrix_mul g h)

@[simp] theorem blockSwap_coe (g : Sp11) : (blockSwap g : QuaternionMatrix2) = swapMatrix g := rfl
@[simp] theorem blockSwap_involution (g : Sp11) : blockSwap (blockSwap g) = g :=
  Subtype.ext (swapMatrix_swap g)

def mobiusNumerator (g : QuaternionMatrix2) (q : ℍ) : ℍ := g 0 0*q+g 0 1

theorem denominator_swap (g : Sp11) (q : Sphere) :
    mobiusDenominator (blockSwap g) q = mobiusNumerator g (q⁻¹:Sphere) * (q:ℍ) := by
  simp [mobiusDenominator,mobiusNumerator,swapMatrix,blockSwap_coe,add_mul,mul_assoc,add_comm]

theorem numerator_swap (g : Sp11) (q : Sphere) :
    mobiusNumerator (blockSwap g) q = mobiusDenominator g (q⁻¹:Sphere) * (q:ℍ) := by
  simp [mobiusDenominator,mobiusNumerator,swapMatrix,blockSwap_coe,add_mul,mul_assoc,add_comm]

theorem numerator_normSq (g : Sp11) (q : Sphere) :
    Quaternion.normSq (mobiusNumerator g q) = Quaternion.normSq (mobiusDenominator g q) := by
  have h := mobius_sphere_normSq g q
  have hn := Quaternion.normSq_ne_zero.mpr
    (denominator_ne_zero_closed g (q := (q:ℍ)) (by simp))
  change Quaternion.normSq (mobiusNumerator g q * (mobiusDenominator g q)⁻¹) = 1 at h
  rw [map_mul,map_inv₀,← div_eq_mul_inv] at h
  exact (div_eq_one_iff_eq hn).mp h

theorem sphereAction_blockSwap (g : Sp11) (q : Sphere) :
    sphereAction (blockSwap g) q = (sphereAction g q⁻¹)⁻¹ := by
  have hq : (q:ℍ) ≠ 0 := by
    intro hz
    have h := Fueter.unitQuaternion_norm q
    rw [hz,norm_zero] at h
    norm_num at h
  apply Subtype.ext
  rw [Unitary.coe_inv,sphereAction_val,sphereAction_val]
  change mobiusNumerator (blockSwap g) q * (mobiusDenominator (blockSwap g) q)⁻¹ =
    (mobiusNumerator g (q⁻¹:Sphere) * (mobiusDenominator g (q⁻¹:Sphere))⁻¹)⁻¹
  rw [numerator_swap,denominator_swap,mul_inv_rev,mul_inv_rev,inv_inv]
  simp only [mul_assoc,mul_inv_cancel_left₀ hq]

theorem normSq_denominator_swap (g : Sp11) (q : Sphere) :
    Quaternion.normSq (mobiusDenominator (blockSwap g) q) =
      Quaternion.normSq (mobiusDenominator g (q⁻¹:Sphere)) := by
  rw [denominator_swap,map_mul,Fueter.unitQuaternion_normSq,mul_one,numerator_normSq]

theorem kelvin_boundaryPull (g : Sp11) (f : Sphere → Fiber) :
    kelvin (boundaryPull g (kelvin f)) = boundaryPull (blockSwap g) f := by
  funext q
  apply toQuaternion_injective
  have hJ := denominator_ne_zero_closed g (q := ((q⁻¹:Sphere):ℍ)) (by simp)
  simp only [kelvin_formula,boundaryPull,toQuaternion_real_smul,toQuaternion_action]
  rw [← Fueter.unitQuaternion_coe_inv,← Fueter.unitQuaternion_coe_inv,
    sphereAction_blockSwap,normSq_denominator_swap]
  simp only [Algebra.mul_smul_comm]
  congr 1
  rw [Unitary.coe_inv (sphereAction g q⁻¹),sphereAction_val]
  change (q⁻¹:Sphere).val * ((mobiusDenominator g (q⁻¹:Sphere))⁻¹ *
    ((mobiusNumerator g (q⁻¹:Sphere) * (mobiusDenominator g (q⁻¹:Sphere))⁻¹)⁻¹ * _)) = _
  rw [mul_inv_rev,inv_inv,denominator_swap,mul_inv_rev,← Unitary.coe_inv q]
  simp only [mul_assoc,inv_mul_cancel_left₀ hJ]

theorem kelvin_boundaryAction (g : Sp11) (f : Sphere → Fiber) :
    kelvin (boundaryAction g (kelvin f)) = boundaryAction (blockSwap g) f := by
  simpa only [boundaryAction,map_inv] using kelvin_boundaryPull g⁻¹ f

end MathResearch.Hardy
