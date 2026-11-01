module
import all MathResearch
import all MathResearch.Analysis.HarmonicPartials
import all MathResearch.Analysis.RadialLaplacian
import all MathResearch.Analysis.SmoothDistribution
import all MathResearch.Analysis.WeylApproximation
import all MathResearch.Analysis.WeylKernel
import all MathResearch.Analysis.WeylProfile
import all MathResearch.Analysis.WeylRepresentative
import all MathResearch.Analysis.WeylTests
import all MathResearch.Fueter.CoefficientRepresentation
import all MathResearch.Fueter.Elliptic
import all MathResearch.Fueter.EllipticCoefficients
import all MathResearch.Fueter.EllipticDilation
import all MathResearch.Fueter.EllipticEstimates
import all MathResearch.Fueter.EllipticPeriodicity
import all MathResearch.Fueter.EllipticRegularity
import all MathResearch.Fueter.HalfPeriods
import all MathResearch.Fueter.HarmonicPolynomial
import all MathResearch.Fueter.HarmonicTheta
import all MathResearch.Fueter.Kernel
import all MathResearch.Fueter.KernelEstimates
import all MathResearch.Fueter.KernelNumerator
import all MathResearch.Fueter.KernelRotationAction
import all MathResearch.Fueter.LatticeDilation
import all MathResearch.Fueter.LatticeSums
import all MathResearch.Fueter.Operators
import all MathResearch.Fueter.PartialCommutation
import all MathResearch.Fueter.PolynomialCalculus
import all MathResearch.Fueter.PuncturedSmooth
import all MathResearch.Fueter.QuaternionRotations
import all MathResearch.Fueter.RealMellin
import all MathResearch.Fueter.RotationCovariance
import all MathResearch.Fueter.SeriesCalculus
import all MathResearch.Fueter.Zeta
import all MathResearch.Fueter.ZetaEstimates
import all MathResearch.Fueter.ZetaQuasiperiods
import all MathResearch.Fueter.ZetaSummands
import all MathResearch.SmokeTest
import all MathResearch.Spinor.BallAction
import all MathResearch.Spinor.BallConnection
import all MathResearch.Spinor.BinaryForm
import all MathResearch.Spinor.ClassicalRow
import all MathResearch.Spinor.ClassicalWeak
import all MathResearch.Spinor.CoefficientEmbedding
import all MathResearch.Spinor.CompactAveraging
import all MathResearch.Spinor.CompactContinuity
import all MathResearch.Spinor.CompactDensity
import all MathResearch.Spinor.CompatibleRow
import all MathResearch.Spinor.CurvatureWitness
import all MathResearch.Spinor.DiscreteSeriesModel
import all MathResearch.Spinor.FrameLift
import all MathResearch.Spinor.FullLift
import all MathResearch.Spinor.GradientIsometry
import all MathResearch.Spinor.GroupKernel
import all MathResearch.Spinor.InteriorEvaluation
import all MathResearch.Spinor.L2StrongContinuity
import all MathResearch.Spinor.LocalClosure
import all MathResearch.Spinor.LocalL2
import all MathResearch.Spinor.MobiusJacobian
import all MathResearch.Spinor.MobiusLaws
import all MathResearch.Spinor.MobiusMeasure
import all MathResearch.Spinor.OrthonormalContraction
import all MathResearch.Spinor.PolynomialRepresentation
import all MathResearch.Spinor.PolynomialUnitary
import all MathResearch.Spinor.ProbabilityMeasure
import all MathResearch.Spinor.ProjectedConnection
import all MathResearch.Spinor.QuaternionMatrix
import all MathResearch.Spinor.RegularAction
import all MathResearch.Spinor.RegularEvaluation
import all MathResearch.Spinor.RegularRowAction
import all MathResearch.Spinor.RepresentationCalculus
import all MathResearch.Spinor.RowAction
import all MathResearch.Spinor.RowWeakEquation
import all MathResearch.Spinor.SchmidCovariance
import all MathResearch.Spinor.SchmidFueter
import all MathResearch.Spinor.SmoothCorrespondence
import all MathResearch.Spinor.Sp11
import all MathResearch.Spinor.WeakConstants
import all MathResearch.Spinor.WeakHarmonic
import all MathResearch.Spinor.WeakKernel
import all MathResearch.Spinor.WeakRowSpace
import all MathResearch.Spinor.WeightedFueter
import all MathResearch.Spinor.WeightedL2Action
import all MathResearch.Spinor.WeightedLocalization
import all MathResearch.Spinor.WeightedMeasure
import all MathResearch.Spinor.WeylBridge
import all MathResearch.Spinor.WeylRegularity
public meta import Lean

open Lean Elab Command

-- Check actual local proof dependencies, not merely which modules are imported.
-- Upstream declarations cannot depend on this downstream project's declarations.
elab "#check_ds2_proof_route" : command => do
  let env ← getEnv
  let roots := #[``MathResearch.Spinor.DS2_v1, ``MathResearch.Spinor.regularPartials_integral]
  let forbidden := #[
    ``MathResearch.Spinor.continuous_weightedL2Action_boundedContinuous,
    ``MathResearch.Spinor.continuous_weightedL2Representation,
    ``MathResearch.Spinor.stronglyContinuous_weightedL2Representation,
    ``MathResearch.Spinor.stronglyContinuous_regularRepresentation]
  let required := #[
    ``MathResearch.Spinor.dense_compactContinuousBallClasses,
    ``MathResearch.Spinor.continuousAt_one_weightedL2Action_compact,
    ``MathResearch.Spinor.weighted_integral_ballAction,
    ``MathResearch.Spinor.weakKernel_isClosed_by_localL2,
    ``MathResearch.Spinor.weylRegularityOnBall,
    ``MathResearch.Spinor.mem_weakRowKernel_iff_distribution,
    ``MathResearch.Spinor.regularRowRepresentation_ae,
    ``MathResearch.Spinor.harmonicPartials_test_formula]
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!.toString
    unless mod == "MathResearch" || mod.startsWith "MathResearch." do continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing dependency {name}"
    for dep in info.getUsedConstantsAsSet do todo := todo.push dep
  for name in forbidden do
    if seen.contains name then throwError "DS2 still depends on the old continuity alternative: {name}"
  for name in required do
    unless seen.contains name do throwError "Expected canonical proof dependency is absent: {name}"
  liftIO <| IO.println ("DS2_PROOF_ROUTE " ++ (Json.mkObj [
    ("status", toJson "passed"),
    ("roots", toJson (roots.map Name.toString)),
    ("required_present", toJson (required.map Name.toString)),
    ("forbidden_absent", toJson (forbidden.map Name.toString)),
    ("local_dependencies", toJson (seen.toList.map Name.toString))]).compress)

#check_ds2_proof_route
