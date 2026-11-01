module
public import MathResearch.Hardy.BoundaryL2
public import Mathlib.Topology.Algebra.MvPolynomial

/-! The actual finite-radial-norm Fueter condition and the closed boundary
polynomial space. No representation-theoretic classification is built into
these definitions. Values outside the open ball are immaterial. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Hardy
open Spinor

def IsRegular (f : ℍ → Fiber) : Prop :=
  ContDiffOn ℝ ∞ f Ball ∧ ∀ q ∈ Ball, Fueter.leftOperator (fun x => toQuaternion (f x)) q = 0

def radialSquareMean (f : ℍ → Fiber) (r : ℝ) : ℝ :=
  ∫ q : Sphere, ‖f (r • (q:ℍ))‖^2 ∂unitQuaternionHaar

def IsHardy (f : ℍ → Fiber) : Prop :=
  IsRegular f ∧ ∃ C : ℝ, ∀ r ∈ Set.Ioo (0:ℝ) 1, radialSquareMean f r ≤ C

/-- Squared Hardy norm; IsHardy supplies boundedness of this nonempty set. -/
def hardyNormSq (f : ℍ → Fiber) : ℝ :=
  sSup {a : ℝ | ∃ r ∈ Set.Ioo (0:ℝ) 1, a = radialSquareMean f r}

/-- Polynomial in the four real coordinates, with two complex coefficients. -/
def IsPolynomial (f : ℍ → Fiber) : Prop :=
  ∃ P : Fin 2 → MvPolynomial (Fin 4) ℂ,
    ∀ q, coefficients 1 (f q) = fun j => (P j).eval (fun i => (Fueter.coordinateBasis.repr q i : ℂ))

/-- Continuous polynomial representatives are included explicitly; this avoids
any tacit measurability choice in the L² generator. -/
def PolynomialBoundaryVector (v : BoundaryL2) : Prop :=
  ∃ f : ℍ → Fiber, IsPolynomial f ∧ Continuous f ∧ IsRegular f ∧
    (v : Sphere → Fiber) =ᵐ[unitQuaternionHaar] (fun q => f q)

def hardyBoundary : Submodule ℂ BoundaryL2 :=
  (Submodule.span ℂ {v | PolynomialBoundaryVector v}).topologicalClosure

abbrev HardyBoundary := hardyBoundary

instance : CompleteSpace HardyBoundary :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The usual boundary limit is an L² radial limit, not an arbitrary identification. -/
def IsBoundaryTrace (f : ℍ → Fiber) (v : BoundaryL2) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 1-δ < r → r < 1 → 0 < r →
    (∫ q : Sphere, ‖f (r • (q:ℍ)) - v q‖^2 ∂unitQuaternionHaar) < ε

end MathResearch.Hardy
