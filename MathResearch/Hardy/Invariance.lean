module
public import MathResearch.Analysis.RegularPolynomialApproximation
public import MathResearch.Hardy.Representation

/-! The written invariance step: polynomial approximation, SC3 covariance,
then closure under the already verified unitary boundary action. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Quaternion
namespace MathResearch.Hardy
open Spinor

theorem continuousTrace_mem_hardy (approximation : RegularPolynomialBoundaryApproximation)
    (f : ℍ → Fiber) (hc : ContinuousOn f (Metric.closedBall (0:ℍ) 1)) (hr : IsRegular f) :
    ContinuousMap.toLp 2 unitQuaternionHaar ℂ (closedBallBoundaryMap f hc) ∈ hardyBoundary := by
  have ha := approximation f hc hr
  have him := image_closure_subset_closure_image
    (s := {F : C(Sphere,Fiber) | RegularPolynomialBoundaryMap F})
    (ContinuousMap.toLp (E := Fiber) 2 unitQuaternionHaar ℂ).continuous
  apply closure_minimal ?_ (Submodule.isClosed_topologicalClosure _) (him ⟨_,ha,rfl⟩)
  rintro _ ⟨F,⟨P,hP,hC,hR,hE⟩,rfl⟩
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨P,hP,hC,hR,?_⟩
  exact (F.coeFn_toLp (p := 2) (𝕜 := ℂ) unitQuaternionHaar).trans
    (Filter.Eventually.of_forall hE)

theorem polynomialAction_mem_hardy (area : BoundaryAreaFormula)
    (approximation : RegularPolynomialBoundaryApproximation) (g : Sp11)
    (v : BoundaryL2) (hv : PolynomialBoundaryVector v) :
    boundaryRepresentation area g v ∈ hardyBoundary := by
  obtain ⟨P,_hP,hC,hR,hE⟩ := hv
  have hc := continuousOn_ballRepresentation_closed g hC
  have hm := continuousTrace_mem_hardy approximation (ballRepresentation 1 g P) hc (hR.action g)
  have he : boundaryRepresentation area g v =
      ContinuousMap.toLp 2 unitQuaternionHaar ℂ (closedBallBoundaryMap (ballRepresentation 1 g P) hc) := by
    apply Lp.ext
    have ha := (sphere_quasiMeasurePreserving area g⁻¹).ae hE
    filter_upwards [boundaryL2Action_ae area g v,ha,
      (closedBallBoundaryMap (ballRepresentation 1 g P) hc).coeFn_toLp (p := 2) (𝕜 := ℂ) unitQuaternionHaar]
      with q h1 h2 h3
    change boundaryL2Action area g v q = _
    rw [h1,h3]
    change boundaryPull g⁻¹ v q = ballRepresentation 1 g P q
    simp only [boundaryPull,h2,sphereAction_val,ballRepresentation,ballAction,Sp11.coe_inv]
  rwa [he]

theorem hardyInvariant_of_polynomialApproximation (area : BoundaryAreaFormula)
    (approximation : RegularPolynomialBoundaryApproximation) : HardyInvariant area := by
  intro g v hv
  let T := hardyBoundary.comap (boundaryRepresentation area g).toLinearEquiv.toLinearMap
  have hs : Submodule.span ℂ {v | PolynomialBoundaryVector v} ≤ T := by
    apply Submodule.span_le.mpr
    exact fun w hw => polynomialAction_mem_hardy area approximation g w hw
  exact (Submodule.topologicalClosure_minimal _ hs
    ((Submodule.isClosed_topologicalClosure _).preimage (boundaryRepresentation area g).continuous)) hv

end MathResearch.Hardy
