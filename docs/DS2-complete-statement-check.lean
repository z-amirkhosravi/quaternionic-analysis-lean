module
import MathResearch

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped Quaternion ContDiff Distributions
open MeasureTheory MathResearch.Spinor

#check DS2_v1
#print DS2_v1
#print regularRepresentation
#print regularRowRepresentation
#print regularRowUnitary
#print rowBallRepresentation
#print rowBallAction
#print rowSubstitution
#print RowDistributionRegular
#print rowWeakTest
#print rowWeakTest_eq_distribution
#print compactContinuousBallClasses
#print realDirectionalPartials
#print partialAdjointTest
#check regularPartialEvaluation_eq_representative
#check regularPartials_bound
#check regularPartials_integral
#check weightedBallMeasure_isProbability
#check regularKernel_complete_by_localL2
#check regularRow_smooth_harmonic_classical
#print axioms DS2_v1
#print axioms continuous_weightedL2Representation_by_compact
#print axioms regularPartials_integral
#print axioms weightedBallMeasure_univ
#print axioms rowWeakTest_eq_distribution

-- n=2 is m=1; the endpoint n=1 is deliberately excluded.
example : CompleteSpace (WeakBallSpace 2 (by omega)) := (DS2_v1 1 (by omega)).1
example : IsProbabilityMeasure (weightedBallMeasure 2) := weightedBallMeasure_isProbability 2 (by omega)

-- The two actions are actual unitary group homomorphisms on the stated Hilbert spaces.
example (m : ℕ) (hm : 1 ≤ m) : Sp11 →* (weakRowKernel m hm ≃ₗᵢ[ℂ] weakRowKernel m hm) :=
  regularRowRepresentation m hm
example (n : ℕ) (hn : 2 ≤ n) (g : Sp11) (f : WeakBallSpace n hn) :
    ‖regularRepresentation n hn g f‖ = ‖f‖ := (regularRepresentation n hn g).norm_map f
example (m : ℕ) (hm : 1 ≤ m) (g : Sp11) (h : weakRowKernel m hm) :
    ‖regularRowRepresentation m hm g h‖ = ‖h‖ := (regularRowRepresentation m hm g).norm_map h

-- Interior support is part of the approximating class, including topological support.
example (n : ℕ) (f : BallL2 n) (hf : f ∈ compactContinuousBallClasses n) :
    ∃ F : ℍ → BinaryForm n, Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ball ∧
      ∃ hF : MemLp F 2 (weightedBallMeasure n), f = hF.toLp F := hf

-- Every real coordinate mixed partial is included; derivative order is explicit.
example (v w : ℍ) (F : ℍ → ℂ) (a : ℍ) :
    realDirectionalPartials [v,w] F a = fderiv ℝ (fun q => fderiv ℝ F q w) a v := rfl
example (n : ℕ) (hn : 2 ≤ n) (coords : List (Fin 4)) (a : ℍ) (ha : a ∈ Ball)
    (f : WeakBallSpace n hn) :
    ‖realDirectionalPartials (coords.map MathResearch.Fueter.coordinateBasis)
      (weylRepresentative (f.val : ℍ → BinaryForm n)) a‖ ≤
      ‖regularPartialEvaluation n hn (coords.map MathResearch.Fueter.coordinateBasis) a ha‖ * ‖f‖ :=
  regularPartials_bound n hn _ a ha f

-- Both normalization factors are those in C4/C6.
example (n : ℕ) (q : ℍ) : ballDensity n q =
    ((n:ℝ)*(n-1:ℝ)/Real.pi^2) * ballScale q^(n-2) := rfl
example (m : ℕ) (p : BinaryForm (m+1)) (k : Fin (m+1)) :
    quaternionCoefficients m (spinorIsometry m p).val k =
      (m+1:ℝ)⁻¹ • fueterCoefficients m p k := quaternionCoefficients_spinorIsometry m p k
