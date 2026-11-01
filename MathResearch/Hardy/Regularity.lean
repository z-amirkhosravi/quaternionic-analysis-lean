module
public import MathResearch.Hardy.Space

/-! The degree-one specialization of the existing SC3 covariance theorem.
No new proof of conformal covariance is inserted into the Hardy argument. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff
namespace MathResearch.Hardy
open Spinor

theorem degreeZero_eq_C (p : BinaryForm 0) :
    (p:ComplexPoly2) = MvPolynomial.C (coefficients 0 p 0) := by
  have h := congrArg Subtype.val (monomialForm_expansion 0 p).symm
  simpa [Fin.sum_univ_one,monomialForm,exponent,MvPolynomial.smul_eq_C_mul] using h

theorem fueterCoefficient_one (p : Fiber) (d : Fin 2 →₀ ℕ) :
    fueterCoefficientCLM 1 d p = if d = 0 then toQuaternion p else 0 := by
  classical
  change pack ((derivative 0 0 p : ComplexPoly2).coeff d) ((derivative 0 1 p : ComplexPoly2).coeff d) = _
  rw [degreeZero_eq_C,degreeZero_eq_C,coefficient_derivative_X,coefficient_derivative_Y]
  by_cases hd : d = 0
  · simp [hd,toQuaternion]
  · simp [MvPolynomial.coeff_C,hd,Ne.symm hd,pack]

theorem IsRegular.action (g : Sp11) {f : ℍ → Fiber} (hf : IsRegular f) :
    IsRegular (ballRepresentation 1 g f) := by
  refine ⟨contDiffOn_ballRepresentation 1 hf.1 g,?_⟩
  have hD : ∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM 1 d (f x)) q = 0 := by
    intro q hq d
    by_cases hd : d = 0
    · simpa only [fueterCoefficient_one,hd,ite_true] using hf.2 q hq
    · simp_rw [fueterCoefficient_one,ite_eq_right hd]
      simp [Fueter.leftOperator]
  have h := SC3_representation_covariance_v1 1 (by omega) f
    (fun q hq => ((hf.1 q hq).contDiffAt (ball_isOpen.mem_nhds hq)).differentiableAt (by simp)) hD g.property
  intro q hq
  simpa only [fueterCoefficient_one,ite_true] using h q hq 0

theorem continuousOn_ballRepresentation_closed (g : Sp11) {f : ℍ → Fiber} (hf : Continuous f) :
    ContinuousOn (ballRepresentation 1 g f) (Metric.closedBall (0:ℍ) 1) := by
  have hJ : Continuous (fun q : ℍ => mobiusDenominator (g⁻¹:Sp11) q) :=
    continuous_const.mul continuous_id |>.add continuous_const
  have hi : ContinuousOn (fun q : ℍ => (mobiusDenominator (g⁻¹:Sp11) q)⁻¹)
      (Metric.closedBall (0:ℍ) 1) := hJ.continuousOn.inv₀ (fun q hq =>
    denominator_ne_zero_closed g⁻¹ (by simpa [Metric.mem_closedBall] using hq))
  have hp := hf.comp_continuousOn (continuousOn_mobius_closed g⁻¹)
  have hv := (contDiff_quaternionPolynomialRepresentation 1).continuous.comp_continuousOn (hi.prodMk hp)
  have hw : ContinuousOn (fun q : ℍ => (Quaternion.normSq (mobiusDenominator (g⁻¹:Sp11) q))⁻¹)
      (Metric.closedBall (0:ℍ) 1) := (Quaternion.continuous_normSq.comp hJ).continuousOn.inv₀
    (fun q hq => Quaternion.normSq_ne_zero.mpr (denominator_ne_zero_closed g⁻¹
      (by simpa [Metric.mem_closedBall] using hq)))
  simpa only [Function.comp_def,ballRepresentation,ballAction] using! hw.smul hv

end MathResearch.Hardy
