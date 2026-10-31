module
import MathResearch

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators ENNReal
open MeasureTheory MathResearch.Spinor

-- Scope: partial DS2, conditional DS3/DS4. No DS2_v1, DS3_v1 or DS4_v1 is asserted.
#check quaternionAction_norm
#check mobiusDenominator_cocycle
#check mobiusJacobian
#check ballRepresentation_mul
#check weighted_integral_ballAction
#check weakTest_toLp
#check constantWeakEmbedding_injective
#check DS2_weak_models
#check DS2_row_intertwining
#check DS3_irreducible_of_compactAveraging
#check DS3_dense_translateSpan
#check DS4_coefficient_integral_of_haar_schur
#check DS4_closed_embedding_of_inputs

-- Hypotheses do not appear in an axiom report; display them explicitly.
#print CompactAveragingInputs
#print CompactSchurInput
#print CoefficientHaarInput
#print TopologicallyIrreducible
#print weakKernel
#print weakRowKernel
#print weakSymbol
#print weakTestVector
#print weakTest
#print liftedCoefficient

#print axioms quaternionAction_norm
#print axioms mobiusJacobian
#print axioms weighted_integral_ballAction
#print axioms weakTest_toLp
#print axioms DS2_weak_models
#print axioms DS2_row_intertwining
#print axioms DS3_irreducible_of_compactAveraging
#print axioms DS4_closed_embedding_of_inputs

-- Small, inspectable definition correspondences.
example (n : ℕ) : weightConstant n = (n:ℝ)*((n:ℝ)-1)/Real.pi^2 := rfl
example (n : ℕ) (q : ℍ) : ballDensity n q =
    ((n:ℝ)*((n:ℝ)-1)/Real.pi^2) * (1-Quaternion.normSq q)^(n-2) := rfl
example (n : ℕ) : weightedBallMeasure n =
    (volume.restrict Ball).withDensity (fun q => ENNReal.ofReal (ballDensity n q)) := rfl
example (n : ℕ) (hn : 2 ≤ n) (f : BallL2 n) :
    f ∈ weakKernel n hn ↔ ∀ φ j d, weakTest n hn φ j d f = 0 := mem_weakKernel n hn f
example (n : ℕ) (μ : Fin 4) (j : Fin 2) (d : Fin 2 →₀ ℕ) (p : BinaryForm n) :
    weakSymbol n μ j d p = (matrixColumn (quaternionMatrix (MathResearch.Fueter.coordinateBasis μ))
      (fun i => MvPolynomial.pderiv i (p : ComplexPoly2)) j).coeff d := rfl
example (m : ℕ) (M : Matrix2) (h : Fin (m+1) → ℍ) (k : Fin (m+1)) :
    rowSubstitution m M h k = ∑ l, h l * ((coefficientActionMatrix m M).transpose l k : ℍ) := rfl
example (m : ℕ) (p : BinaryForm (m+1)) (k : Fin (m+1)) :
    normalizedFueterRow m p k = (m+1:ℝ)⁻¹ •
      pack ((MvPolynomial.pderiv 0 (p : ComplexPoly2)).coeff (exponent m k))
        ((MvPolynomial.pderiv 1 (p : ComplexPoly2)).coeff (exponent m k)) := rfl
example (n : ℕ) (v : BinaryForm n) (f : ℍ → BinaryForm n) (g : Sp11) :
    liftedCoefficient n v f g = inner ℂ v (fullLift n f g) := rfl

-- The first degree n=2 is included; no positive-degree endpoint is silently dropped.
example : Nontrivial (WeakBallSpace 2 (by omega)) := inferInstance
example : CompleteSpace (weakRowKernel 1 (by omega)) := inferInstance
example (f : ℍ → BinaryForm 2) (g : QuaternionMatrix2) (q : ℍ) (k : Fin 2) :
    normalizedFueterRow 1 (ballRepresentation 2 g f q) k =
      rowBallRepresentation 1 g (fun x => normalizedFueterRow 1 (f x)) q k :=
  DS2_row_intertwining 1 g f q k
