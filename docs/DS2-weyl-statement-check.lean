module
import MathResearch

noncomputable section
set_option autoImplicit false
open scoped Quaternion Distributions ContDiff
open MeasureTheory InnerProductSpace MathResearch.Spinor

-- Exact statement and definition inspection; no complete DS2_v1 is asserted.
#check smooth_harmonic_representative
#check weylRegularityOnBall
#check weakKernel_smoothRepresentative
#check mem_weakKernel_iff_classicalFueter
#check weakKernel_classicalRepresentative
#check weightedL2Action_mem_weakKernel
#check stronglyContinuous_regularRepresentation
#check regularEvaluation_eq_representative
#check regularEvaluation_bound
#check mem_weakRowKernel_iff_classical
#print WeylRegularityOnBall
#print distributionLaplacian
#print weylRepresentative
#print weylScaledKernel
#print regularRepresentation
#print regularUnitary
#print regularEvaluation
#print HasClassicalRowRepresentative
#print rowCoefficient
#print rowCoefficient_spinorIsometry

#print axioms smooth_harmonic_representative
#print axioms weylRegularityOnBall
#print axioms weakKernel_smoothRepresentative
#print axioms mem_weakKernel_iff_classicalFueter
#print axioms weightedL2Action_mem_weakKernel
#print axioms stronglyContinuous_regularRepresentation
#print axioms regularEvaluation_eq_representative
#print axioms regularEvaluation_bound
#print axioms mem_weakRowKernel_iff_classical

-- The premise is discharged, rather than restated as a new assumption.
example : WeylRegularityOnBall (BinaryForm 2) := weylRegularityOnBall _
example {u : ℍ → ℂ} (hu : LocallyIntegrableOn u Ball volume)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0) :
    ContDiffOn ℝ ∞ (weylRepresentative u) Ball ∧
      HarmonicOnNhd (weylRepresentative u) Ball ∧
      u =ᵐ[volume.restrict Ball] weylRepresentative u :=
  smooth_harmonic_representative hu hΔ

-- The first allowed degree has the actual strongly continuous unitary action.
example : Sp11 →* (WeakBallSpace 2 (by omega) ≃ₗᵢ[ℂ] WeakBallSpace 2 (by omega)) :=
  regularRepresentation 2 (by omega)
example (f : WeakBallSpace 2 (by omega)) :
    Continuous (fun g : Sp11 => regularRepresentation 2 (by omega) g f) :=
  stronglyContinuous_regularRepresentation 2 (by omega) f

-- Normalization and A-jB coefficient convention are inspectable independently.
example (m : ℕ) (d : Fin 2 →₀ ℕ) (h : CompatibleRow m) :
    rowCoefficient m d h =
      pack ((h.val 0 : ComplexPoly2).coeff d) ((h.val 1 : ComplexPoly2).coeff d) := rfl
example (m : ℕ) (d : Fin 2 →₀ ℕ) (p : BinaryForm (m+1)) :
    rowCoefficient m d (spinorIsometry m p) =
      (m+1:ℝ)⁻¹ • fueterCoefficientCLM (m+1) d p :=
  rowCoefficient_spinorIsometry m d p

-- Evaluation belongs to the unique continuous representative, not an arbitrary L² function.
example (a : ℍ) (ha : a ∈ Ball) (f : WeakBallSpace 2 (by omega))
    {F : ℍ → BinaryForm 2} (hF : ContinuousOn F Ball)
    (he : (f.val : ℍ → BinaryForm 2) =ᵐ[weightedBallMeasure 2] F) :
    regularEvaluation 2 (by omega) a ha f = F a :=
  regularEvaluation_eq_representative 2 (by omega) a ha f hF he
