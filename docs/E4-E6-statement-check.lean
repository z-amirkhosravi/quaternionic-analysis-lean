import MathResearch
open scoped Quaternion Topology BigOperators ContDiff
open MathResearch.Fueter
#check @E4_v1
#check @E5_v1
#check @E6_v1
#print realDilation
#print dilatedLattice
#print latticeDilationEquiv
#check @mem_dilatedLattice
#check @smul_mem_dilatedLattice
#check @latticeDilationEquiv_apply
#check @elliptic_fderiv_halfPeriod
#check @kernel_fderiv_smul_apply
#print axioms MathResearch.Fueter.E4_v1
#print axioms MathResearch.Fueter.E5_v1
#print axioms MathResearch.Fueter.E6_v1

-- For any real basis, a basis vector supplies an actual nonlattice half-period.
-- This checks that the half-period condition is realizable, without an arithmetic restriction.
private theorem half_basis_not_mem (b : Module.Basis (Fin 4) ℝ ℍ) (i : Fin 4) :
    (2 : ℝ)⁻¹ • b i ∉ Submodule.span ℤ (Set.range b) := by
  intro h
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  have hz' : (z : ℝ) = (2 : ℝ)⁻¹ := by simpa using hz
  have hz0 : (0 : ℝ) < z := by rw [hz']; norm_num
  have hz1 : (z : ℝ) < 1 := by rw [hz']; norm_num
  have h0 : 0 < z := by exact_mod_cast hz0
  have h1 : z < 1 := by exact_mod_cast hz1
  omega

example (b : Module.Basis (Fin 4) ℝ ℍ) :
    let L := Submodule.span ℤ (Set.range b)
    let w : L := ⟨b 0, Submodule.subset_span ⟨0, rfl⟩⟩
    zetaQuasiperiod L w = (2 : ℝ) • zeta L ((2 : ℝ)⁻¹ • b 0) ∧
    ∀ j : Fin 3, HasFDerivAt (elliptic L j) (0 : ℍ →L[ℝ] ℍ) ((2 : ℝ)⁻¹ • b 0) := by
  dsimp only
  exact ⟨E4_v1 _ _ (half_basis_not_mem b 0),
    fun j => (E5_v1 (Submodule.span ℤ (Set.range b)) j ⟨b 0, Submodule.subset_span ⟨0, rfl⟩⟩ (half_basis_not_mem b 0)).1⟩

-- E5 includes the time coordinate explicitly.
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]
    (j : Fin 3) (w : L) (hw : (2 : ℝ)⁻¹ • (w : ℍ) ∉ L) :
    coordPartial 0 (elliptic L j) ((2 : ℝ)⁻¹ • (w : ℍ)) = 0 := (E5_v1 L j w hw).2 0

-- Dilation carries an arbitrary real-basis lattice to a discrete, full-rank lattice.
example (b : Module.Basis (Fin 4) ℝ ℍ) (a : ℝ) (ha : 0 < a) :
    DiscreteTopology (dilatedLattice (Submodule.span ℤ (Set.range b)) a ha.ne') := inferInstance
example (b : Module.Basis (Fin 4) ℝ ℍ) (a : ℝ) (ha : 0 < a) :
    IsZLattice ℝ (dilatedLattice (Submodule.span ℤ (Set.range b)) a ha.ne') := inferInstance

-- The argument aq is in the correct off-lattice domain; the period index really is aw.
example (L : Submodule ℤ ℍ) (a : ℝ) (ha : 0 < a) (q : ℍ) (hq : q ∉ L) :
    a • q ∉ dilatedLattice L a ha.ne' := by simpa using hq
example (L : Submodule ℤ ℍ) (a : ℝ) (ha : 0 < a) (w : L) :
    (latticeDilationEquiv L a ha.ne' w : ℍ) = a • (w : ℍ) := rfl

-- All three E6 conclusions apply without a separately assumed scaled-lattice instance.
example (b : Module.Basis (Fin 4) ℝ ℍ) (a : ℝ) (ha : 0 < a)
    (j : Fin 3) (q : ℍ) (hq : q ∉ Submodule.span ℤ (Set.range b))
    (w : Submodule.span ℤ (Set.range b)) :
    elliptic (dilatedLattice (Submodule.span ℤ (Set.range b)) a ha.ne') j (a • q) =
        (a ^ 4)⁻¹ • elliptic (Submodule.span ℤ (Set.range b)) j q ∧
    zeta (dilatedLattice (Submodule.span ℤ (Set.range b)) a ha.ne') (a • q) =
        (a ^ 3)⁻¹ • zeta (Submodule.span ℤ (Set.range b)) q ∧
    zetaQuasiperiod (dilatedLattice (Submodule.span ℤ (Set.range b)) a ha.ne')
        (latticeDilationEquiv (Submodule.span ℤ (Set.range b)) a ha.ne' w) =
        (a ^ 3)⁻¹ • zetaQuasiperiod (Submodule.span ℤ (Set.range b)) w := E6_v1 _ a ha j q hq w
