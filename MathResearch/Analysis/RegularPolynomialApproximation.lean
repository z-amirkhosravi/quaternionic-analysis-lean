module
public import MathResearch.Hardy.Regularity

/-! OPEN approximation theorem used at the Hardy invariance step.
This is the sup-norm boundary consequence of the regular homogeneous expansion:
dilate a function continuous on the closed ball, then approximate the dilate
by its regular polynomial partial sums. The complete proof belongs here,
separately from the research invariance argument. -/
@[expose] public section
noncomputable section
open scoped Quaternion
namespace MathResearch.Hardy
open Spinor

def RegularPolynomialBoundaryMap (F : C(Sphere,Fiber)) : Prop :=
  ∃ f : ℍ → Fiber, IsPolynomial f ∧ Continuous f ∧ IsRegular f ∧ ∀ q : Sphere, F q = f q

def closedBallBoundaryMap (f : ℍ → Fiber)
    (hc : ContinuousOn f (Metric.closedBall (0:ℍ) 1)) : C(Sphere,Fiber) :=
  ⟨fun q => f q,hc.comp_continuous continuous_subtype_val (fun q => by simp [Metric.mem_closedBall])⟩

/-- Sup-norm approximation, with genuine regular polynomial approximants.
This is a theorem interface only; no proof, axiom or instance supplies it. -/
def RegularPolynomialBoundaryApproximation : Prop :=
  ∀ (f : ℍ → Fiber) (hc : ContinuousOn f (Metric.closedBall (0:ℍ) 1)), IsRegular f →
    closedBallBoundaryMap f hc ∈ closure {F | RegularPolynomialBoundaryMap F}

end MathResearch.Hardy
