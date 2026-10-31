module
import MathResearch

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion Distributions ContDiff
open MeasureTheory MathResearch.Spinor

-- No declaration of a complete DS2_v1 is asserted.
#check memLp_locallyIntegrableOn_ball
#check spinorDistribution_injective
#check weakKernel_distribution_fueter
#check testLaplacian_eq
#check weakKernel_distributionLaplacian_zero
#check weightedL2_tendsto_locally
#check weakTest_eq_local
#check weakKernel_closed_under_localL2_limits
#check weakKernel_isClosed_by_localL2
#check mobius_map_jacobian
#check mobius_quasiMeasurePreserving_weighted
#check ballAction_memLp
#check ballRepresentation_mul_by_cocycle
#check weightedL2Action_ae
#check weightedL2Representation
#check continuous_weightedL2Representation
#check stronglyContinuous_weightedL2Representation
#check weakKernel_smoothRepresentative_of_weyl
#check continuousRepresentative_unique

-- The input is visible in the signature; an axiom audit cannot discharge it.
#print WeylRegularityOnBall
#print spinorDistribution
#print testDirectional
#print testLaplacian
#print distributionLaplacian
#print weightedL2Action
#print weightedL2Unitary
#print weightedL2Representation

#print axioms weakKernel_distributionLaplacian_zero
#print axioms weakKernel_isClosed_by_localL2
#print axioms weightedL2Representation
#print axioms stronglyContinuous_weightedL2Representation
#print axioms weakKernel_smoothRepresentative_of_weyl

-- The first admissible weight is included, and the group is the actual Sp(1,1).
example : Sp11 →* (BallL2 2 ≃ₗᵢ[ℂ] BallL2 2) := weightedL2Representation 2 (by omega)
example (f : BallL2 2) : Continuous (fun g : Sp11 => weightedL2Representation 2 (by omega) g f) :=
  stronglyContinuous_weightedL2Representation 2 (by omega) f

-- Ordinary derivatives and the actual weighted measure are exposed.
example (φ : BallTest) (v q : ℍ) : testDirectional v φ q = fderiv ℝ φ q v :=
  testDirectional_apply v φ q
example (n : ℕ) (f : BallL2 n) : spinorDistribution n f =
    Distribution.ofFun ballOpen (fun q => f q) volume ⊤ := rfl

-- No uniqueness outside B is asserted.
example (n : ℕ) (hn : 2 ≤ n) {u v : ℍ → BinaryForm n}
    (hu : ContDiffOn ℝ ∞ u Ball) (hv : ContDiffOn ℝ ∞ v Ball)
    (he : u =ᵐ[weightedBallMeasure n] v) : Set.EqOn u v Ball :=
  continuousRepresentative_unique n hn hu.continuousOn hv.continuousOn he
