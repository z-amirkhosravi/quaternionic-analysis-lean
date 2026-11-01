module
public import MathResearch.Hardy.Space
public import MathResearch.Spinor.RegularOrbit

/-! The lowest compact type consists of genuine constant Fueter functions. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
open MeasureTheory
namespace MathResearch.Hardy
open Spinor

def constantBoundary : Fiber →ₗᵢ[ℂ] BoundaryL2 where
  toLinearMap := Lp.constₗ 2 unitQuaternionHaar ℂ
  norm_map' v := by
    change ‖Lp.const 2 unitQuaternionHaar v‖ = ‖v‖
    rw [Lp.norm_const _ _ _ (by norm_num)]
    simp

theorem constantBoundary_ae (v : Fiber) :
    (constantBoundary v : Sphere → Fiber) =ᵐ[unitQuaternionHaar] (fun _ => v) := Lp.coeFn_const 2 unitQuaternionHaar _

theorem constant_polynomial (v : Fiber) : IsPolynomial (fun _ => v) := by
  refine ⟨fun j => MvPolynomial.C (coefficients 1 v j),?_⟩
  intro q
  funext j
  simp

theorem constant_regular (v : Fiber) : IsRegular (fun _ => v) := by
  refine ⟨contDiffOn_const,?_⟩
  intro q _
  simp [Fueter.leftOperator,Fueter.leftContraction]

@[simp] theorem radialSquareMean_constant (v : Fiber) (r : ℝ) :
    radialSquareMean (fun _ => v) r = ‖v‖^2 := by simp [radialSquareMean]

theorem constant_isHardy (v : Fiber) : IsHardy (fun _ => v) :=
  ⟨constant_regular v,‖v‖^2,fun r _ => (radialSquareMean_constant v r).le⟩

theorem hardyNormSq_constant (v : Fiber) : hardyNormSq (fun _ => v) = ‖v‖^2 := by
  have he : {a : ℝ | ∃ r ∈ Set.Ioo (0:ℝ) 1, a = radialSquareMean (fun _ => v) r} = {‖v‖^2} := by
    ext a
    constructor
    · rintro ⟨r,_,rfl⟩
      simp
    · intro ha
      refine ⟨1/2,by norm_num,?_⟩
      simpa only [radialSquareMean_constant,Set.mem_singleton_iff] using ha
  rw [hardyNormSq,he,csSup_singleton]

theorem constantBoundary_mem (v : Fiber) : constantBoundary v ∈ hardyBoundary := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨fun _ => v,constant_polynomial v,continuous_const,constant_regular v,constantBoundary_ae v⟩

def constantHardy : Fiber →ₗᵢ[ℂ] HardyBoundary where
  toFun v := ⟨constantBoundary v,constantBoundary_mem v⟩
  map_add' v w := Subtype.ext (map_add constantBoundary v w)
  map_smul' z v := Subtype.ext (map_smul constantBoundary z v)
  norm_map' v := constantBoundary.norm_map v

instance fiber_nontrivial : Nontrivial Fiber := (coefficientEquiv 1).symm.injective.nontrivial
instance hardyBoundary_nontrivial : Nontrivial HardyBoundary := constantHardy.injective.nontrivial

theorem boundaryAction_constant_compact (area : BoundaryAreaFormula) (a b : Sphere) (v : Fiber) :
    boundaryRepresentation area (compactSp11 (a,b)) (constantBoundary v) =
      constantBoundary (polynomialRepresentation 1 (quaternionMatrix b) v) := by
  apply Lp.ext
  have ha := (sphere_quasiMeasurePreserving area (compactSp11 (a,b))⁻¹).ae (constantBoundary_ae v)
  filter_upwards [boundaryL2Action_ae area (compactSp11 (a,b)) (constantBoundary v),ha,
    constantBoundary_ae (polynomialRepresentation 1 (quaternionMatrix b) v)] with q h1 h2 h3
  change boundaryL2Action area (compactSp11 (a,b)) (constantBoundary v) q = _
  rw [h1,h3]
  simp only [boundaryAction,boundaryPull,h2]
  exact ballRepresentation_compact 1 a b (fun _ => v) q

end MathResearch.Hardy
