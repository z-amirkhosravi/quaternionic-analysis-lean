module
import MathResearch.Spinor.BallConnection
import MathResearch.Analysis.MaurerCartan
noncomputable section
open scoped Quaternion BigOperators Matrix.Norms.Elementwise Topology
open MathResearch.Spinor
set_option pp.funBinderTypes true

#check MathResearch.Analysis.maurerCartan
#check ballSection_maurerCartan
#check ballCurvature_eq
#check projected_full_homogeneous
#check projected_connection_homogeneous
#check SC2_v1
#print axioms MathResearch.Analysis.maurerCartan
#print axioms ballCurvature_eq
#print axioms projected_connection_homogeneous

-- The curvature target has precisely its original statement, with all real directions.
example (q v w : ℍ) (hq : q ∈ Ball) :
    ballCurvature q v w = -(ballScale q)⁻¹ ^ 2 • (star v * w - star w * v) :=
  ballCurvature_eq q v w hq

-- The second target retains its full all-degree polynomial-column statement.
example (m : ℕ) (q : ℍ) (p : BinaryForm (m + 1)) (i : Fin 2) :
    (∑ μ : Fin 4, matrixColumn (quaternionMatrix (MathResearch.Fueter.coordinateBasis μ))
      (fun j => MvPolynomial.pderiv j (infinitesimal (quaternionMatrix
        (connectionCoefficient q (MathResearch.Fueter.coordinateBasis μ))) p)) i) =
    (m + 3 : ℂ) • matrixColumn (quaternionMatrix q)
      (fun j => MvPolynomial.pderiv j (p : ComplexPoly2)) i :=
  projected_connection_homogeneous m q p i

-- Inspect the specialized background interface used by SC1; its hypotheses are explicit.
example (f g : ℍ → QuaternionMatrix2) (q v w : ℍ)
    (hf : ContDiffAt ℝ 2 f q) (hg : DifferentiableAt ℝ g q)
    (hgf : (fun y => g y * f y) =ᶠ[𝓝 q] fun _ => 1) (hfg : f q * g q = 1) :
    fderiv ℝ (fun y => g y * fderiv ℝ f y w) q v -
      fderiv ℝ (fun y => g y * fderiv ℝ f y v) q w +
      (g q * fderiv ℝ f q v * (g q * fderiv ℝ f q w) -
       g q * fderiv ℝ f q w * (g q * fderiv ℝ f q v)) = 0 :=
  MathResearch.Analysis.maurerCartan hf hg hgf hfg v w
