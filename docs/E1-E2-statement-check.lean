import MathResearch
open scoped Quaternion Topology BigOperators
open MathResearch.Fueter
#check @E1_v2
#check @E2_v2
#print elliptic
#print regularizedJet
#print kernelJet
#print iteratedPartial
#print TwoSidedRegularOn
#check @elliptic_iteratedPartial
#check @elliptic_regular_remainder
#print axioms MathResearch.Fueter.E1_v2
#print axioms MathResearch.Fueter.E2_v2
-- Every real basis generates an admissible full lattice.
example (b : Module.Basis (Fin 4) ℝ ℍ) (j : Fin 3) :
    TwoSidedRegularOn (elliptic (Submodule.span ℤ (Set.range b)) j)
      (Submodule.span ℤ (Set.range b) : Set ℍ)ᶜ := (E1_v2 _ j).2.2.2.1
example (b : Module.Basis (Fin 4) ℝ ℍ) (j : Fin 3) (q : ℍ)
    (hq : q ∉ Submodule.span ℤ (Set.range b)) (w : Submodule.span ℤ (Set.range b)) :
    elliptic (Submodule.span ℤ (Set.range b)) j (q + (w : ℍ)) =
      elliptic (Submodule.span ℤ (Set.range b)) j q := (E2_v2 _ j q hq w).2
-- E1's list quantifier includes every real multi-index (time coordinate included).
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]
    (j : Fin 3) (α : Fin 4 → ℕ) :
    HasSumLocallyUniformlyOn
      (fun a : L => multiIndexPartial α (regularizedJet j [] (a : ℍ)))
      (multiIndexPartial α (elliptic L j)) (L : Set ℍ)ᶜ := by
  unfold multiIndexPartial
  exact (E1_v2 L j).2.2.1 _
-- The pole assertion includes the origin, not only nonzero lattice points.
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L] (j : Fin 3) :
    ∃ U : Set ℍ, IsOpen U ∧ (0 : ℍ) ∈ U ∧ ∃ r : ℍ → ℍ,
      TwoSidedRegularOn r U ∧ ∀ q ∈ U, q ∉ L →
        r q = elliptic L j q - kernelSpatialPartial j q := by
  simpa using (E1_v2 L j).2.2.2.2 (0 : L)
