module
public import MathResearch.Analysis.CompactHaarSymmetry
public import MathResearch.Analysis.QuaternionicHaarCoordinates

/-! The actual boundary sphere action, using the unit-quaternion realization of S³. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion Matrix.Norms.Elementwise
open Set MeasureTheory
namespace MathResearch.Hardy
open Spinor
abbrev Sphere := Fueter.UnitQuaternion

theorem denominator_ne_zero_closed (g : Sp11) {q : ℍ} (hq : ‖q‖ ≤ 1) :
    mobiusDenominator g q ≠ 0 := by
  have h := g.property.row_norms
  rw [Quaternion.normSq_eq_norm_mul_self,Quaternion.normSq_eq_norm_mul_self] at h
  have hd : ‖g.val 1 0‖ < ‖g.val 1 1‖ := by
    nlinarith [norm_nonneg (g.val 1 0),norm_nonneg (g.val 1 1)]
  intro hz
  have he : g.val 1 0*q = -g.val 1 1 := eq_neg_of_add_eq_zero_left hz
  have hn := congrArg norm he
  rw [norm_mul,norm_neg] at hn
  have H := mul_le_mul_of_nonneg_left hq (norm_nonneg (g.val 1 0))
  nlinarith

theorem continuousOn_mobius_closed (g : Sp11) :
    ContinuousOn (mobiusPoint g) (Metric.closedBall (0:ℍ) 1) := by
  apply ContinuousOn.mul
  · exact (continuous_const.mul continuous_id |>.add continuous_const).continuousOn
  · apply ContinuousOn.inv₀
    · exact (continuous_const.mul continuous_id |>.add continuous_const).continuousOn
    · intro q hq
      exact denominator_ne_zero_closed g (by simpa only [Metric.mem_closedBall,dist_zero_right] using hq)

theorem ballScale_mobius_closed (g : Sp11) {q : ℍ} (hq : ‖q‖ ≤ 1) :
    ballScale (mobiusPoint g q) = ballScale q / Quaternion.normSq (mobiusDenominator g q) := by
  have hb : Ball = Metric.ball (0:ℍ) 1 := Set.ext (fun q => by
    simpa only [Metric.mem_ball,dist_zero_right] using mem_ball_iff q)
  have he : Set.EqOn (fun q => ballScale (mobiusPoint g q))
      (fun q => ballScale q / Quaternion.normSq (mobiusDenominator g q)) Ball :=
    fun q hq => ballScale_mobius g.property hq
  apply he.of_subset_closure
    (contDiff_ballScale.continuous.comp_continuousOn (continuousOn_mobius_closed g))
    (contDiff_ballScale.continuous.continuousOn.div
      (Quaternion.continuous_normSq.comp (continuous_const.mul continuous_id |>.add continuous_const)).continuousOn
      (fun q hq => Quaternion.normSq_ne_zero.mpr (denominator_ne_zero_closed g (by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hq))))
  · rw [hb]; exact Metric.ball_subset_closedBall
  · rw [hb,closure_ball (0:ℍ) (by norm_num : (1:ℝ) ≠ 0)]
  · simpa only [Metric.mem_closedBall,dist_zero_right] using hq

theorem mobius_sphere_normSq (g : Sp11) (q : Sphere) :
    Quaternion.normSq (mobiusPoint g q) = 1 := by
  have h := ballScale_mobius_closed g (q := (q:ℍ)) (by rw [Fueter.unitQuaternion_norm])
  simp only [ballScale,Fueter.unitQuaternion_normSq,sub_self,zero_div] at h
  linarith

def sphereAction (g : Sp11) (q : Sphere) : Sphere :=
  unitQuaternionOfNormSq (mobiusPoint g q) (mobius_sphere_normSq g q)

@[simp] theorem sphereAction_val (g : Sp11) (q : Sphere) :
    (sphereAction g q : ℍ) = mobiusPoint g q := rfl

@[simp] theorem sphereAction_one (q : Sphere) : sphereAction 1 q = q :=
  Subtype.ext (mobiusPoint_one q)

theorem sphereAction_mul (g h : Sp11) (q : Sphere) :
    sphereAction (g*h) q = sphereAction g (sphereAction h q) :=
  Subtype.ext (mobiusPoint_mul g h (denominator_ne_zero_closed h (by rw [Fueter.unitQuaternion_norm])))

theorem continuous_sphereAction (g : Sp11) : Continuous (sphereAction g) := by
  apply Continuous.subtype_mk
  exact (continuousOn_mobius_closed g).comp_continuous continuous_subtype_val
    (fun q => by simp [Metric.mem_closedBall])

def sphereHomeomorph (g : Sp11) : Sphere ≃ₜ Sphere where
  toFun := sphereAction g
  invFun := sphereAction g⁻¹
  left_inv q := by rw [← sphereAction_mul,inv_mul_cancel,sphereAction_one]
  right_inv q := by rw [← sphereAction_mul,mul_inv_cancel,sphereAction_one]
  continuous_toFun := continuous_sphereAction g
  continuous_invFun := continuous_sphereAction g⁻¹

/-- The conformal three-dimensional area factor |cq+d|⁻⁶. -/
def boundaryJacobian (g : Sp11) (q : Sphere) : ℝ :=
  (Quaternion.normSq (mobiusDenominator g q))⁻¹ ^ 3

theorem boundaryJacobian_pos (g : Sp11) (q : Sphere) : 0 < boundaryJacobian g q := by
  have hn := norm_pos_iff.mpr (denominator_ne_zero_closed g (q := (q:ℍ))
    (by rw [Fueter.unitQuaternion_norm]))
  unfold boundaryJacobian
  rw [Quaternion.normSq_eq_norm_mul_self]
  positivity

theorem continuous_boundaryJacobian (g : Sp11) : Continuous (boundaryJacobian g) := by
  apply Continuous.pow
  apply Continuous.inv₀
  · exact Quaternion.continuous_normSq.comp
      (continuous_const.mul continuous_subtype_val |>.add continuous_const)
  · intro q
    exact Quaternion.normSq_ne_zero.mpr (denominator_ne_zero_closed g (by rw [Fueter.unitQuaternion_norm]))

end MathResearch.Hardy
