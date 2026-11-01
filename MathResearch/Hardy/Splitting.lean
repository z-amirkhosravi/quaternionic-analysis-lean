module
public import MathResearch.Analysis.SpinorCompactExpansion

/-! H2's orthogonal splitting, conditional on the named open compact expansion
inputs. Kelvin intertwining and the Hilbert closure deduction are proved here. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
namespace MathResearch.Hardy
open Spinor

theorem blockSwap_compact (a b : Sphere) : blockSwap (compactSp11 (a,b)) = compactSp11 (b,a) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [compactSp11,compactMatrix,swapMatrix]

theorem negativeCompact_equivariant (area : BoundaryAreaFormula)
    (kt : SpinorCompactExpansionData area) (m : ℕ) (a b : Sphere) (v : PositiveCompactType m) :
    boundaryRepresentation area (compactSp11 (a,b)) (kelvinUnitary (kt.positive m v)) =
      kelvinUnitary (kt.positive m (positiveCompactAction m (b,a) v)) := by
  have h := kelvinL2_intertwining area (compactSp11 (b,a)) (kelvinUnitary (kt.positive m v))
  rw [kelvinUnitary_apply_apply,blockSwap_compact,kt.equivariant] at h
  exact h.symm

theorem H2_orthogonal_splitting_of_compactExpansion (area : BoundaryAreaFormula)
    (kt : SpinorCompactExpansionData area) :
    hardyBoundary ≤ negativeHardyBoundaryᗮ ∧
    (hardyBoundary ⊔ negativeHardyBoundary).topologicalClosure = ⊤ := by
  let S : Submodule ℂ BoundaryL2 := ⨆ m, LinearMap.range (kt.positive m).toLinearMap
  have hs : S.topologicalClosure = hardyBoundary := kt.hardy_span
  have hcross : S ≤ (S.map kelvinUnitary.toLinearEquiv.toLinearMap)ᗮ := by
    dsimp only [S]
    rw [Submodule.map_iSup,← Submodule.iInf_orthogonal]
    apply le_iInf
    intro n
    apply iSup_le
    intro m
    rintro _ ⟨v,rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨_,⟨w,rfl⟩,rfl⟩
    exact (inner_eq_zero_symm).mpr (kt.cross_orthogonal m n v w)
  have hc : S.topologicalClosure ≤ (S.map kelvinUnitary.toLinearEquiv.toLinearMap)ᗮ :=
    S.topologicalClosure_minimal hcross (Submodule.isClosed_orthogonal _)
  have hm := Submodule.topologicalClosure_map kelvinUnitary.toContinuousLinearEquiv.toContinuousLinearMap S
  have ho := Submodule.orthogonal_le hm
  rw [Submodule.orthogonal_closure] at ho
  constructor
  · change hardyBoundary ≤ (hardyBoundary.map kelvinUnitary.toLinearEquiv.toLinearMap)ᗮ
    rw [← hs]
    exact hc.trans ho
  · apply le_antisymm le_top
    rw [← kt.boundary_span]
    apply Submodule.topologicalClosure_mono
    apply sup_le_sup
    · rw [← hs]; exact S.le_topologicalClosure
    · apply Submodule.map_mono
      rw [← hs]; exact S.le_topologicalClosure

end MathResearch.Hardy
