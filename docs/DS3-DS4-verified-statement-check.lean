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
#print normalizedGroupHaar
#print ballInvariantMeasure
#print invariantBallDensity
#print groupFromBallCoordinates
#print ballSectionPoint
#print quotientHaarAverage
#print compactHaar
#print unitQuaternionHaar
#print regularCoefficient
#print coefficientNormConstant
#print leftL2Representation
#check groupBallHomeomorph
#check normalizedGroupHaar_isHaar
#check sphericalMeanValueOnBall_proved
#check radialMeanValueOnBall_proved
#check quotientHaarIntegration_proved
#check DS3_v1
#check DS3_row_v1
#check DS4_v1
#check DS4_polynomialEmbedding
#check DS4_rowEmbedding
#check DS4_row_v1
#check DS4_coefficient_formula
#print axioms sphericalMeanValueOnBall_proved
#print axioms radialMeanValueOnBall_proved
#print axioms quotientHaarIntegration_proved
#print axioms DS3_v1
#print axioms DS4_v1
#print axioms DS4_row_v1

-- No unverified mean-value premise, including at the smallest research degree.
example : TopologicallyIrreducible (regularRepresentation 2 (by omega)) :=
  (DS3_v1 1 (by omega)).1

example (v : BinaryForm 2) (f : WeakBallSpace 2 (by omega)) :
    MemLp (regularCoefficient 2 (by omega) v f) 2 normalizedGroupHaar :=
  (DS4_coefficient_formula 1 (by omega) v f).1

-- Genuine row embedding, with no placeholder measure or assumed norm identity.
example (v : BinaryForm 2) (hv : v ≠ 0) :
    weakRowKernel 1 (by omega) →ₗᵢ[ℂ] Lp ℂ 2 normalizedGroupHaar :=
  DS4_rowEmbedding 1 (by omega) v hv

example (n : ℕ) (v : BinaryForm n) : coefficientNormConstant n v =
    ‖v‖^2 / ((n+1:ℝ) * ((n:ℝ)*(n-1:ℝ)/Real.pi^2)) := rfl

-- The written C12 lift identity uses the now-proved radial mean-value theorem.
example (n : ℕ) (hn : 2 ≤ n) (v : BinaryForm n) (f : WeakBallSpace n hn)
    (F : ℍ → BinaryForm n) (hF : ContDiffOn ℝ ∞ F Ball)
    (he : (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) (g : Sp11) :
    regularCoefficient n hn v f g = liftedCoefficient n v F g :=
  regularCoefficient_eq_lift radialMeanValueOnBall_proved n hn v f F hF he g

-- All complete real normed targets, not only scalar-valued functions.
example (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℍ → E) (hF : ContDiffOn ℝ ∞ F Ball)
    (hH : InnerProductSpace.HarmonicOnNhd F Ball) (q : ℍ) (hq : q ∈ Ball) :
    (∫ a : Fueter.UnitQuaternion, F ((a:ℍ)⁻¹*q) ∂unitQuaternionHaar) = F 0 :=
  sphericalMeanValueOnBall_proved E F hF hH q hq

example (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) (hn : 2 ≤ n) (F : ℍ → E) (hF : ContDiffOn ℝ ∞ F Ball)
    (hH : InnerProductSpace.HarmonicOnNhd F Ball) (hI : Integrable F (weightedBallMeasure n)) :
    (∫ q, F q ∂weightedBallMeasure n) = F 0 :=
  radialMeanValueOnBall_proved E n hn F hF hH hI

-- Haar and integrability assertions are proved, not supplied as hypotheses.
example : normalizedGroupHaar.IsHaarMeasure := quotientHaarIntegration_proved.isHaar

example (φ : Sp11 → ℝ) (hc : Continuous φ) (hn : ∀ g, 0 ≤ φ g) :
    Integrable φ normalizedGroupHaar ↔ IntegrableOn (quotientHaarAverage φ) Ball volume :=
  quotientHaarIntegration_proved.integrable_iff φ hc hn

example (φ : Sp11 → ℝ) (hc : Continuous φ) (hn : ∀ g, 0 ≤ φ g) :
    (∫ g, φ g ∂normalizedGroupHaar) = ∫ q in Ball, quotientHaarAverage φ q :=
  quotientHaarIntegration_proved.integral_formula φ hc hn
