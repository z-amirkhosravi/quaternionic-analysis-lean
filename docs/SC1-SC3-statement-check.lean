module
import MathResearch

noncomputable section
set_option autoImplicit false
open scoped Quaternion Matrix.Norms.Elementwise ContDiff
open MathResearch.Spinor

-- Full signatures, including the regularity and domain hypotheses.
#check SC1_v1
#check SC3_v1
#check SC3_representation_covariance_v1
#check SC3_smooth_correspondence_v1
#print axioms SC1_v1
#print axioms SC3_v1
#print axioms SC3_representation_covariance_v1
#print axioms SC3_smooth_correspondence_v1
#print axioms curvature_origin_action_ne_zero

-- Each of these compares one written convention to its concrete Lean definition.
example (q : ℍ) : q ∈ Ball ↔ ‖q‖ < 1 := mem_ball_iff q
example (q v : ℍ) : ballConnection q v =
    (1 - Quaternion.normSq q)⁻¹ • ((2:ℝ)⁻¹ • (star v*q-star q*v)) := rfl
example (q : ℍ) : ballSection q =
    (Real.sqrt (1-Quaternion.normSq q))⁻¹ • !![1,q;star q,1] := rfl
example (g : QuaternionMatrix2) : IsSp11 g ↔
    signatureAdjoint g*g=1 ∧ g*signatureAdjoint g=1 := Iff.rfl
example (g : QuaternionMatrix2) : signatureAdjoint g =
    !![star (g 0 0),-star (g 1 0);-star (g 0 1),star (g 1 1)] := rfl
example (g : QuaternionMatrix2) (hg : IsSp11 g) :
    g=ballSection (groupOrigin g)*compactMatrix (compactLeft g) (compactRight g) :=
  section_compact_decomposition hg
example (n : ℕ) (f : ℍ → BinaryForm n) (g : QuaternionMatrix2) :
    fullLift n f g=(Quaternion.normSq (g 1 1))⁻¹ •
      polynomialRepresentation n (quaternionMatrix ((g 1 1)⁻¹)) (f (g 0 1*(g 1 1)⁻¹)) := rfl
example (n : ℕ) (f : ℍ → BinaryForm n) (q : ℍ) (hq : q ∈ Ball) :
    fullLift n f (ballSection q)=(1-Quaternion.normSq q)^(((n:ℝ)+2)/2) • f q :=
  fullLift_section n f q hq
example (n : ℕ) (p : BinaryForm n) (d : Fin 2 →₀ ℕ) :
    fueterCoefficientCLM n d p=pack ((MvPolynomial.pderiv 0 (p : ComplexPoly2)).coeff d)
      ((MvPolynomial.pderiv 1 (p : ComplexPoly2)).coeff d) := rfl
example (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n) (g : QuaternionMatrix2) (d : Fin 2 →₀ ℕ) :
    (24:ℝ) • schmidOperator n F g d=projectedGroupOperator n F g d :=
  schmidOperator_normalization n F g d
example : ballCurvature 0 1 (⟨0,1,0,0⟩ : ℍ)=(⟨0,-2,0,0⟩ : ℍ) := ballCurvature_origin
example (m : ℕ) : infinitesimal (quaternionMatrix (ballCurvature 0 1 (⟨0,1,0,0⟩ : ℍ)))
    (MvPolynomial.X 0 ^ (m+1)) ≠ 0 := curvature_origin_action_ne_zero m

-- Agreement with the exponential curve in the wiki, not merely a formal tangent symbol.
open scoped Matrix.Norms.Operator in
example (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n) (g : QuaternionMatrix2)
    (hF : DifferentiableAt ℝ F g) (v : ℍ) :
    deriv (fun t : ℝ => F (g*NormedSpace.exp (t • tangentMatrix v))) 0 = rightLieDerivative n F g v :=
  rightLieDerivative_eq_exp n F g hF v

-- The n=1 endpoint and every polynomial exponent are included.
example (f : ℍ → BinaryForm 1) (hf : ∀ q ∈ Ball, DifferentiableAt ℝ f q) :
    ∀ q ∈ Ball, ∀ d, (24:ℝ) • schmidOperator 1 (fullLift 1 f) (ballSection q) d =
      (ballScale q) ^ (5/2:ℝ) • MathResearch.Fueter.leftOperator
        (fun x => fueterCoefficientCLM 1 d (f x)) q := by
  simpa only [ballWeight, Nat.cast_one, show ((1:ℝ)+4)/2=5/2 by norm_num] using (SC3_v1 1 (by omega) f hf).1

-- The group element is inverted in C7, and quaternion multiplication order is visible.
example (n : ℕ) (γ : QuaternionMatrix2) (f : ℍ → BinaryForm n) (q : ℍ) :
    ballRepresentation n γ f q =
      (Quaternion.normSq ((signatureAdjoint γ) 1 0*q+(signatureAdjoint γ) 1 1))⁻¹ •
        polynomialRepresentation n
          (quaternionMatrix (((signatureAdjoint γ) 1 0*q+(signatureAdjoint γ) 1 1)⁻¹))
          (f (((signatureAdjoint γ) 0 0*q+(signatureAdjoint γ) 0 1)*
            ((signatureAdjoint γ) 1 0*q+(signatureAdjoint γ) 1 1)⁻¹)) := rfl
#check fullLift_ballAction
#check rightLieDerivative_congr_on_group
#check polynomialRepresentation_scalar
