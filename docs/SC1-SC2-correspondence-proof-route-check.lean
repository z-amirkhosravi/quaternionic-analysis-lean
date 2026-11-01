module
import all MathResearch.Analysis.CompactHaarSymmetry
import all MathResearch.Analysis.CompactParametricIntegral
import all MathResearch.Analysis.HarmonicMeanValue
import all MathResearch.Analysis.HarmonicPartials
import all MathResearch.Analysis.InvariantDensity
import all MathResearch.Analysis.LeftRegularL2
import all MathResearch.Analysis.MaurerCartan
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
import all MathResearch.Analysis.RotationalBallMeasure
import all MathResearch.Analysis.SmoothDistribution
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

-- Follow actual constants in theorem values and types, not merely imports.
private meta def localClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut todo := #[root]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!.toString
    unless mod.startsWith "MathResearch." do continue
    seen := seen.insert name
    let some info := env.find? name | continue
    for dep in info.getUsedConstantsAsSet do todo := todo.push dep
  return seen

elab "#check_sc1_sc2_routes" : command => do
  let env ← getEnv
  let routes := #[
    (``MathResearch.Spinor.ballCurvature_eq,
      #[``MathResearch.Analysis.maurerCartan,
        ``MathResearch.Spinor.ballSection_maurerCartan,
        ``MathResearch.Spinor.ballSection_inverse,
        ``MathResearch.Spinor.ballSections_contDiffAt_two],
      #[``MathResearch.Spinor.fderiv_ballConnection]),
    (``MathResearch.Spinor.projected_connection_homogeneous,
      #[``MathResearch.Spinor.projected_full_homogeneous,
        ``MathResearch.Spinor.connectionCoefficient_eq_inner,
        ``MathResearch.Spinor.infinitesimal_quaternion_sub,
        ``MathResearch.Spinor.infinitesimal_real,
        ``MathResearch.Spinor.coordinateBasis_inner_sum,
        ``MathResearch.Spinor.matrixColumn_inner_sum],
      #[``MathResearch.Spinor.projected_connection_identity]),
    (``MathResearch.Spinor.SC2_v1,
      #[``MathResearch.Spinor.projected_connection_homogeneous,
        ``MathResearch.Spinor.projected_full_homogeneous],
      #[``MathResearch.Spinor.projected_connection_identity])]
  for (root, required, forbidden) in routes do
    let seen := localClosure env root
    for name in required do
      unless seen.contains name do throwError "Missing canonical proof inference: {root} -> {name}"
    for name in forbidden do
      if seen.contains name then throwError "Superseded calculation is still used: {root} -> {name}"
    liftIO <| IO.println ("SC1_SC2_PROOF_ROUTE " ++ (Json.mkObj [
      ("root", toJson root.toString), ("status", toJson "passed"),
      ("required_present", toJson (required.map Name.toString)),
      ("forbidden_absent", toJson (forbidden.map Name.toString)),
      ("local_dependencies", toJson ((seen.toList.map Name.toString).mergeSort))]).compress)

#check_sc1_sc2_routes
