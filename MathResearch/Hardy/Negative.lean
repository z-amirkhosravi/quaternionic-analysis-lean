module
public import MathResearch.Hardy.Irreducible
public import MathResearch.Hardy.KelvinIntertwining

/-! The negative Hardy representation is the actual Kelvin image. Irreducibility
transfers by the verified block-swap automorphism, as in the internal proof. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace MathResearch.Hardy
open Spinor

abbrev NegativeHardy := negativeHardyBoundary

def kelvinHardyEquiv : HardyBoundary ≃ₗᵢ[ℂ] NegativeHardy :=
  LinearIsometryEquiv.submoduleMap hardyBoundary kelvinUnitary

instance : CompleteSpace NegativeHardy :=
  kelvinHardyEquiv.toIsometryEquiv.completeSpace_iff.mp inferInstance

def negativeRepresentation (area : BoundaryAreaFormula) (hinv : HardyInvariant area) :
    Sp11 →* (NegativeHardy ≃ₗᵢ[ℂ] NegativeHardy) where
  toFun g := kelvinHardyEquiv.symm.trans
    ((hardyRepresentation area hinv (blockSwap g)).trans kelvinHardyEquiv)
  map_one' := by ext f : 1; simp
  map_mul' g h := by
    ext f : 1
    change kelvinHardyEquiv (hardyRepresentation area hinv (blockSwap (g*h)) (kelvinHardyEquiv.symm f)) =
      kelvinHardyEquiv (hardyRepresentation area hinv (blockSwap g)
        (kelvinHardyEquiv.symm (kelvinHardyEquiv
          (hardyRepresentation area hinv (blockSwap h) (kelvinHardyEquiv.symm f)))))
    simp only [LinearIsometryEquiv.symm_apply_apply,map_mul,LinearIsometryEquiv.coe_mul,Function.comp_apply]

theorem negativeRepresentation_kelvin (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (g : Sp11) (f : HardyBoundary) :
    negativeRepresentation area hinv g (kelvinHardyEquiv f) =
      kelvinHardyEquiv (hardyRepresentation area hinv (blockSwap g) f) := by
  change kelvinHardyEquiv (hardyRepresentation area hinv (blockSwap g)
    (kelvinHardyEquiv.symm (kelvinHardyEquiv f))) = _
  rw [kelvinHardyEquiv.symm_apply_apply]

theorem negativeRepresentation_formula (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (g : Sp11) (f : NegativeHardy) :
    (negativeRepresentation area hinv g f).val = boundaryRepresentation area g f.val := by
  obtain ⟨v,rfl⟩ := kelvinHardyEquiv.surjective f
  rw [negativeRepresentation_kelvin]
  change kelvinUnitary (boundaryRepresentation area (blockSwap g) v.val) =
    boundaryRepresentation area g (kelvinUnitary v.val)
  have h := kelvinL2_intertwining area (blockSwap g) (kelvinUnitary v.val)
  simpa only [kelvinUnitary_apply_apply,blockSwap_involution] using h

theorem stronglyContinuous_negativeRepresentation (area : BoundaryAreaFormula)
    (hinv : HardyInvariant area) (f : NegativeHardy) :
    Continuous (fun g : Sp11 => negativeRepresentation area hinv g f) := by
  have h : Continuous (fun g : Sp11 => (negativeRepresentation area hinv g f).val) := by
    simpa only [negativeRepresentation_formula] using stronglyContinuous_boundaryRepresentation area f.val
  exact Continuous.subtype_mk h _

theorem H2_negative_irreducible_of_traceData (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (tr : HardyTraceData area hinv) : TopologicallyIrreducible (negativeRepresentation area hinv) := by
  let twisted := (hardyRepresentation area hinv).comp blockSwap.toMonoidHom
  have ht : TopologicallyIrreducible twisted := by
    intro M hc hm
    apply (H1_irreducible_of_traceData area hinv tr).1 M hc
    intro g f hf
    have h := hm (blockSwap g) f hf
    change hardyRepresentation area hinv (blockSwap (blockSwap g)) f ∈ M at h
    simpa only [blockSwap_involution] using h
  exact TopologicallyIrreducible.transport twisted (negativeRepresentation area hinv) kelvinHardyEquiv
    (negativeRepresentation_kelvin area hinv) ht

end MathResearch.Hardy
