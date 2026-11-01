module
import MathResearch
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped Quaternion ContDiff
open MeasureTheory MathResearch MathResearch.Spinor

#print SphericalMeanValueOnBall
#print RadialMeanValueOnBall
#print QuotientHaarIntegration
#print regularCoefficient
#print coefficientNormConstant
#print compactHaar
#print unitQuaternionHaar
#print leftL2Representation
#check compactPolynomial_irreducible
#check compactPolynomial_schur
#check compactSchurInput_proved
#check DS3_v1_of_meanValue
#check DS3_row_of_meanValue
#check DS3_row_dense_of_meanValue
#check regularCoefficient_eq_lift
#check regularCoefficient_memLp
#check DS4_v1_of_background
#check regularRowCoefficientIsometry_intertwines
#check regularRowCoefficientIsometry_closed
#print axioms compactPolynomial_irreducible
#print axioms compactPolynomial_schur
#print axioms DS3_v1_of_meanValue
#print axioms DS4_v1_of_background

-- Minimal research degree n=2; the unproved mean-value premise is visible.
example (spherical : SphericalMeanValueOnBall) :
    TopologicallyIrreducible (regularRepresentation 2 (by omega)) :=
  (DS3_v1_of_meanValue spherical 1 (by omega)).1

-- Positive-degree Schur orthogonality has no unverified external premise.
example : CompactSchurInput 2 compactHaar := compactSchurInput_proved 1

-- No assumed L² realization: it is constructed from the standard inputs.
example (radial : RadialMeanValueOnBall) (μG : Measure Sp11)
    (haar : QuotientHaarIntegration μG) (v : BinaryForm 2)
    (f : WeakBallSpace 2 (by omega)) : MemLp (regularCoefficient 2 (by omega) v f) 2 μG :=
  regularCoefficient_memLp radial 2 (by omega) μG haar (compactSchurInput_proved 1) v f

-- The denominator and weight are the exact C13 normalizations.
example (n : ℕ) (v : BinaryForm n) : coefficientNormConstant n v =
    ‖v‖^2 / ((n+1:ℝ) * ((n:ℝ)*(n-1:ℝ)/Real.pi^2)) := rfl

-- The mean-value premise is a general harmonic-function theorem, not a statement
-- that the particular regular representation is irreducible.
example (spherical : SphericalMeanValueOnBall) (F : ℍ → ℂ)
    (hF : ContDiffOn ℝ ∞ F Ball) (hH : InnerProductSpace.HarmonicOnNhd F Ball)
    (q : ℍ) (hq : q ∈ Ball) :
    (∫ a : MathResearch.Fueter.UnitQuaternion, F ((a:ℍ)⁻¹*q) ∂unitQuaternionHaar) = F 0 :=
  spherical ℂ F hF hH q hq

-- The Haar premise applies to every nonnegative continuous function and tracks
-- integrability, not just the displayed totalized coefficient integral.
example (μG : Measure Sp11) (haar : QuotientHaarIntegration μG) (φ : Sp11 → ℝ)
    (hc : Continuous φ) (hn : ∀ g, 0 ≤ φ g) :
    Integrable φ μG ↔ IntegrableOn (quotientHaarAverage φ) Ball volume :=
  haar.integrable_iff φ hc hn
