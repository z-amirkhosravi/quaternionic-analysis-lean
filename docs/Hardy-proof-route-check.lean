module
import all MathResearch.Analysis.BoundaryAreaFormula
import all MathResearch.Analysis.CompactHaarSymmetry
import all MathResearch.Analysis.CompactParametricIntegral
import all MathResearch.Analysis.FueterHardyTrace
import all MathResearch.Analysis.HarmonicMeanValue
import all MathResearch.Analysis.HarmonicPartials
import all MathResearch.Analysis.InvariantDensity
import all MathResearch.Analysis.LeftRegularL2
import all MathResearch.Analysis.QuaternionicHaarCoordinates
import all MathResearch.Analysis.QuaternionicHaarMeasure
import all MathResearch.Analysis.QuaternionicInvariantMeasure
import all MathResearch.Analysis.QuaternionicMeanValue
import all MathResearch.Analysis.QuaternionicQuotientHaar
import all MathResearch.Analysis.QuaternionicRadialMeanValue
import all MathResearch.Analysis.QuaternionicSphericalAverage
import all MathResearch.Analysis.QuotientHaarIntegration
import all MathResearch.Analysis.RadialHarmonic
import all MathResearch.Analysis.RadialHessian
import all MathResearch.Analysis.RadialLaplacian
import all MathResearch.Analysis.RadialMeanODE
import all MathResearch.Analysis.RegularPolynomialApproximation
import all MathResearch.Analysis.RotationalBallMeasure
import all MathResearch.Analysis.SmoothDistribution
import all MathResearch.Analysis.SpinorCompactExpansion
import all MathResearch.Analysis.SpinorEndpointClassification
import all MathResearch.Analysis.UnitaryIrreducible
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
import all MathResearch.Hardy.BlockSwap
import all MathResearch.Hardy.BoundaryAction
import all MathResearch.Hardy.BoundaryGeometry
import all MathResearch.Hardy.BoundaryL2
import all MathResearch.Hardy.Constants
import all MathResearch.Hardy.CompactFormula
import all MathResearch.Hardy.Continuity
import all MathResearch.Hardy.Endpoint
import all MathResearch.Hardy.Fiber
import all MathResearch.Hardy.Invariance
import all MathResearch.Hardy.Irreducible
import all MathResearch.Hardy.Kelvin
import all MathResearch.Hardy.KelvinIntertwining
import all MathResearch.Hardy.Negative
import all MathResearch.Hardy.Normalization
import all MathResearch.Hardy.Regularity
import all MathResearch.Hardy.Representation
import all MathResearch.Hardy.Space
import all MathResearch.Hardy.Splitting
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
import all MathResearch.Spinor.CompactGroup
import all MathResearch.Spinor.CompactIrreducible
import all MathResearch.Spinor.CompactSchur
import all MathResearch.Spinor.CompatibleRow
import all MathResearch.Spinor.CurvatureWitness
import all MathResearch.Spinor.DiscreteSeriesCoefficient
import all MathResearch.Spinor.DiscreteSeriesIrreducible
import all MathResearch.Spinor.DiscreteSeriesModel
import all MathResearch.Spinor.DiscreteSeriesVerified
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
import all MathResearch.Spinor.RegularCoefficient
import all MathResearch.Spinor.RegularEvaluation
import all MathResearch.Spinor.RegularOrbit
import all MathResearch.Spinor.RegularRowAction
import all MathResearch.Spinor.RegularSquareIntegrable
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
elab "#check_hardy_proof_route" : command => do
  let env ← getEnv
  let roots := #[``MathResearch.Hardy.Hardy_endpoint_realization_of_inputs,
    ``MathResearch.Hardy.Hardy_pi1_of_background,
    ``MathResearch.Hardy.boundaryAction_hyperbolic_fixed]
  let forbidden : Array Name := #[]
  let required := #[``MathResearch.Hardy.hardyInvariant_of_polynomialApproximation,
    ``MathResearch.Hardy.IsRegular.action,
    ``MathResearch.Spinor.SC3_representation_covariance_v1,
    ``MathResearch.Hardy.hardy_compact_average,
    ``MathResearch.Spinor.sphericalMeanValueOnBall_proved,
    ``MathResearch.Hardy.hardy_translate_detects,
    ``MathResearch.Spinor.compactPolynomial_irreducible,
    ``MathResearch.Spinor.DS3_irreducible_of_compactAveraging,
    ``MathResearch.Hardy.kelvinL2_intertwining,
    ``MathResearch.Hardy.kelvin_boundaryPull,
    ``MathResearch.Hardy.blockSwap,
    ``MathResearch.Hardy.H2_orthogonal_splitting_of_compactExpansion,
    ``MathResearch.Hardy.H2_negative_irreducible_of_traceData,
    ``MathResearch.Hardy.BoundaryAreaFormula,
    ``MathResearch.Hardy.RegularPolynomialBoundaryApproximation,
    ``MathResearch.Hardy.HardyTraceData,
    ``MathResearch.Hardy.SpinorCompactExpansionData,
    ``MathResearch.Hardy.SpinorEndpointClassification,
    ``MathResearch.Hardy.boundaryRepresentation,
    ``MathResearch.Hardy.continuous_boundaryRepresentation,
    ``MathResearch.Hardy.boundaryAction_hyperbolic_fixed]
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
    if seen.contains name then throwError "Forbidden proof dependency: {name}"
  for name in required do
    unless seen.contains name do throwError "Expected canonical proof dependency is absent: {name}"
  liftIO <| IO.println ("HARDY_CONDITIONAL_PROOF_ROUTE " ++ (Json.mkObj [
    ("status", toJson "passed"),
    ("roots", toJson (roots.map Name.toString)),
    ("required_present", toJson (required.map Name.toString)),
    ("forbidden_absent", toJson (forbidden.map Name.toString)),
    ("local_dependencies", toJson (seen.toList.map Name.toString))]).compress)

#check_hardy_proof_route
