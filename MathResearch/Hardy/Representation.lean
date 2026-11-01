module
public import MathResearch.Hardy.Constants
public import MathResearch.Hardy.Continuity

/-! Restriction to the independently defined closed polynomial space.
The analytic invariance bridge is an explicit hypothesis. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathResearch.Hardy
open Spinor

abbrev HardyInvariant (area : BoundaryAreaFormula) : Prop :=
  UnitaryInvariant (boundaryRepresentation area) hardyBoundary

def hardyUnitary (area : BoundaryAreaFormula) (hinv : HardyInvariant area) (g : Sp11) :
    HardyBoundary ≃ₗᵢ[ℂ] HardyBoundary where
  toFun f := ⟨boundaryRepresentation area g f.val,hinv g f.val f.property⟩
  invFun f := ⟨boundaryRepresentation area g⁻¹ f.val,hinv g⁻¹ f.val f.property⟩
  map_add' f h := Subtype.ext (map_add (boundaryRepresentation area g) f.val h.val)
  map_smul' z f := Subtype.ext (map_smul (boundaryRepresentation area g) z f.val)
  left_inv f := by
    apply Subtype.ext
    change boundaryL2Action area g⁻¹ (boundaryL2Action area g f.val) = f.val
    rw [← boundaryL2Action_mul,inv_mul_cancel,boundaryL2Action_one]
  right_inv f := by
    apply Subtype.ext
    change boundaryL2Action area g (boundaryL2Action area g⁻¹ f.val) = f.val
    rw [← boundaryL2Action_mul,mul_inv_cancel,boundaryL2Action_one]
  norm_map' f := boundaryL2Action_norm area g f.val

def hardyRepresentation (area : BoundaryAreaFormula) (hinv : HardyInvariant area) :
    Sp11 →* (HardyBoundary ≃ₗᵢ[ℂ] HardyBoundary) where
  toFun := hardyUnitary area hinv
  map_one' := by ext f : 1; exact Subtype.ext (boundaryL2Action_one area f.val)
  map_mul' g h := by ext f : 1; exact Subtype.ext (boundaryL2Action_mul area g h f.val)

theorem stronglyContinuous_hardyRepresentation (area : BoundaryAreaFormula)
    (hinv : HardyInvariant area) (f : HardyBoundary) :
    Continuous (fun g : Sp11 => hardyRepresentation area hinv g f) :=
  Continuous.subtype_mk (stronglyContinuous_boundaryRepresentation area f.val) _

theorem hardyAction_constant_compact (area : BoundaryAreaFormula) (hinv : HardyInvariant area)
    (a b : Sphere) (v : Fiber) :
    hardyRepresentation area hinv (compactSp11 (a,b)) (constantHardy v) =
      constantHardy (polynomialRepresentation 1 (quaternionMatrix b) v) :=
  Subtype.ext (boundaryAction_constant_compact area a b v)

end MathResearch.Hardy
