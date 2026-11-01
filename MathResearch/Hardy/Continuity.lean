module
public import MathResearch.Hardy.BoundaryL2

/-! Strong continuity: continuous boundary functions form a dense class on the
compact sphere; continuity there extends by the verified L² isometries. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion
open MeasureTheory
namespace MathResearch.Hardy
open Spinor

theorem continuous_boundaryAction_joint (f : C(Sphere,Fiber)) :
    Continuous (fun z : Sp11 × Sphere => boundaryAction z.1 f z.2) := by
  have hm : Continuous (fun z : Sp11 × Sphere => signatureAdjoint z.1) :=
    continuous_signatureAdjoint.comp (continuous_sp11_coe.comp continuous_fst)
  have he (i j : Fin 2) : Continuous (fun z : Sp11 × Sphere => (signatureAdjoint z.1) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hm)
  have hq : Continuous (fun z : Sp11 × Sphere => (z.2:ℍ)) := continuous_subtype_val.comp continuous_snd
  have hJ : Continuous (fun z : Sp11 × Sphere => mobiusDenominator (z.1⁻¹ : Sp11) z.2) :=
    ((he 1 0).mul hq).add (he 1 1)
  have hn (z : Sp11 × Sphere) : mobiusDenominator (z.1⁻¹ : Sp11) z.2 ≠ 0 :=
    denominator_ne_zero_closed _ (by simp)
  have hi := hJ.inv₀ hn
  have hp : Continuous (fun z : Sp11 × Sphere => sphereAction z.1⁻¹ z.2) :=
    Continuous.subtype_mk ((((he 0 0).mul hq).add (he 0 1)).mul hi) _
  have hv := (contDiff_quaternionPolynomialRepresentation 1).continuous.comp
    (hi.prodMk (f.continuous.comp hp))
  have hw := (Quaternion.continuous_normSq.comp hJ).inv₀
    (fun z => Quaternion.normSq_ne_zero.mpr (hn z))
  simpa only [boundaryAction,boundaryPull,Function.comp_def] using! hw.smul hv

def boundaryContinuousAction (g : Sp11) (f : C(Sphere,Fiber)) : C(Sphere,Fiber) :=
  ⟨boundaryAction g f,by
    simpa only [Function.comp_def] using (continuous_boundaryAction_joint f).comp
      (continuous_const.prodMk continuous_id : Continuous (fun q : Sphere => (g,q)))⟩

theorem continuous_boundaryContinuousAction (f : C(Sphere,Fiber)) :
    Continuous (fun g : Sp11 => boundaryContinuousAction g f) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_boundaryAction_joint f)

theorem boundaryL2Action_continuousMap (area : BoundaryAreaFormula) (g : Sp11) (f : C(Sphere,Fiber)) :
    boundaryL2Action area g (ContinuousMap.toLp 2 unitQuaternionHaar ℂ f) =
      ContinuousMap.toLp 2 unitQuaternionHaar ℂ (boundaryContinuousAction g f) := by
  apply Lp.ext
  have ha := (sphere_quasiMeasurePreserving area g⁻¹).ae (f.coeFn_toLp (p := 2) (𝕜 := ℂ) unitQuaternionHaar)
  filter_upwards [boundaryL2Action_ae area g (ContinuousMap.toLp 2 unitQuaternionHaar ℂ f),
    (boundaryContinuousAction g f).coeFn_toLp (p := 2) (𝕜 := ℂ) unitQuaternionHaar,ha] with q h1 h2 h3
  rw [h1,h2]
  change boundaryAction g _ q = boundaryAction g f q
  simp only [boundaryAction,boundaryPull,h3]

theorem continuous_boundaryRepresentation (area : BoundaryAreaFormula) :
    Continuous (fun z : BoundaryL2 × Sp11 => boundaryRepresentation area z.2 z.1) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (ContinuousMap.toLp_denseRange Fiber unitQuaternionHaar (p := 2) ℂ (by norm_num))
  · rintro f ⟨F,rfl⟩
    change Continuous (fun g => boundaryL2Action area g (ContinuousMap.toLp 2 unitQuaternionHaar ℂ F))
    simp_rw [boundaryL2Action_continuousMap]
    exact (ContinuousMap.toLp 2 unitQuaternionHaar ℂ).continuous.comp (continuous_boundaryContinuousAction F)
  · intro g
    exact (boundaryUnitary area g).isometry.lipschitzWith

theorem stronglyContinuous_boundaryRepresentation (area : BoundaryAreaFormula) (f : BoundaryL2) :
    Continuous (fun g : Sp11 => boundaryRepresentation area g f) := by
  simpa only [Function.comp_def] using (continuous_boundaryRepresentation area).comp
    (continuous_const.prodMk continuous_id : Continuous (fun g : Sp11 => (f,g)))

end MathResearch.Hardy
