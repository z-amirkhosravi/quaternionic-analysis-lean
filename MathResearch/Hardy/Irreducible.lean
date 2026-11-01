module
public import MathResearch.Analysis.FueterHardyTrace
public import MathResearch.Analysis.QuaternionicMeanValue
public import MathResearch.Analysis.UnitaryIrreducible
public import MathResearch.Spinor.CompactIrreducible

/-! The internal Hardy irreducibility argument, in its original order:
compact averaging via spherical mean values, translate detection at zero,
irreducibility of constants, and the orthogonal complement.
The OPEN area, invariance and trace inputs remain visible. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Hardy
open Spinor

def hardyOrigin {area : BoundaryAreaFormula} {hinv : HardyInvariant area}
    (tr : HardyTraceData area hinv) : HardyBoundary →L[ℂ] Fiber :=
  tr.evaluation 0 (by simp [Ball,ballScale])

theorem hardy_compactOrbit_integrable (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (f : HardyBoundary) : Integrable
      (fun a => hardyRepresentation area hinv (compactLeftSp11 a) f) unitQuaternionHaar :=
  ((stronglyContinuous_hardyRepresentation area hinv f).comp continuous_compactLeftSp11).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem hardy_compact_average (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (tr : HardyTraceData area hinv) (f : HardyBoundary) :
    (∫ a, hardyRepresentation area hinv (compactLeftSp11 a) f ∂unitQuaternionHaar) =
      constantHardy (hardyOrigin tr f) := by
  obtain ⟨F,hF,hH,he,_htrace,_hnorm⟩ := tr.representative f
  apply tr.evaluation_ext
  intro q hq
  rw [tr.constant_value]
  rw [← (tr.evaluation q hq).integral_comp_comm (hardy_compactOrbit_integrable area hinv f)]
  have hp (a : Sphere) : tr.evaluation q hq
      (hardyRepresentation area hinv (compactLeftSp11 a) f) = F ((a:ℍ)⁻¹*q) := by
    rw [tr.action_value _ _ F hF.1 he]
    change ballRepresentation 1 (compactSp11 (a,1)) F q = _
    simpa [quaternionMatrix_one] using ballRepresentation_compact 1 a 1 F q
  simp_rw [hp]
  rw [sphericalMeanValueOnBall_proved Fiber F hF.1.1 hH q hq]
  exact (he 0 _).symm

theorem hardy_translate_detects (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (tr : HardyTraceData area hinv) (f : HardyBoundary) (hf : f ≠ 0) :
    ∃ g : Sp11, hardyOrigin tr (hardyRepresentation area hinv g f) ≠ 0 := by
  obtain ⟨F,hF,_hH,he,_htrace,_hnorm⟩ := tr.representative f
  have hex : ∃ q ∈ Ball, F q ≠ 0 := by
    by_contra hx
    apply hf
    apply tr.evaluation_ext
    intro q hq
    rw [he q hq,(tr.evaluation q hq).map_zero]
    exact not_ne_iff.mp (fun hh => hx ⟨q,hq,hh⟩)
  obtain ⟨q,hq,hFq⟩ := hex
  let s : Sp11 := ⟨ballSection q,ballSection_isSp11 q hq⟩
  refine ⟨s⁻¹,?_⟩
  rw [hardyOrigin,tr.action_value _ _ F hF.1 he]
  change ballAction 1 (signatureAdjoint (signatureAdjoint (ballSection q))) F 0 ≠ 0
  rw [signatureAdjoint_involutive,ballAction_zero_eq_fullLift,fullLift_section 1 F q hq]
  exact smul_ne_zero (ballWeight_pos _ hq).ne' hFq

theorem hardy_constant_orbit_spans (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (v : Fiber) (hv : v ≠ 0) :
    LinearMap.range constantHardy.toLinearMap ≤ Submodule.span ℂ
      (Set.range fun g : Sp11 => hardyRepresentation area hinv g (constantHardy v)) :=
  equivariant_irreducible_range_le_span (hardyRepresentation area hinv) constantHardy
    (fun a : Sphere => polynomialRepresentation 1 (quaternionMatrix a))
    (fun a => compactSp11 (1,a))
    (fun a p => (hardyAction_constant_compact area hinv 1 a p).symm)
    (compactPolynomial_irreducible 0) v hv

/-- Conditional H1 irreducibility, with the actual finite-radial-norm function
realization included. This does not assert that the open trace inputs or the
limit-of-discrete-series classification have been proved. -/
theorem H1_irreducible_of_traceData (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (tr : HardyTraceData area hinv) :
    TopologicallyIrreducible (hardyRepresentation area hinv) ∧
    (∀ f : HardyBoundary, Continuous (fun g : Sp11 => hardyRepresentation area hinv g f)) ∧
    (∀ F : ℍ → Fiber, IsHardy F → ∃ f : HardyBoundary,
      (∀ q (hq : q ∈ Ball), tr.evaluation q hq f = F q) ∧
      IsBoundaryTrace F f.val ∧ hardyNormSq F = ‖f‖^2) := by
  let : Nontrivial Fiber := (coefficientEquiv 1).symm.injective.nontrivial
  refine ⟨DS3_irreducible_of_compactAveraging (hardyRepresentation area hinv)
    unitQuaternionHaar compactLeftSp11 constantHardy (hardyOrigin tr) ?_,
    stronglyContinuous_hardyRepresentation area hinv,tr.realization⟩
  exact ⟨hardy_compactOrbit_integrable area hinv,hardy_compact_average area hinv tr,
    hardy_translate_detects area hinv tr,hardy_constant_orbit_spans area hinv⟩

end MathResearch.Hardy
