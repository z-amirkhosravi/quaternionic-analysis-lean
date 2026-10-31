import MathResearch
open scoped Quaternion Topology BigOperators ContDiff
open MathResearch.Fueter
#check @E3_v2
#print zeta
#print zetaJet
#print coordPartial
#print iteratedPartial
#print TwoSidedRegularOn
#print zetaQuasiperiod
#check @zetaJet_zero
#check @zetaJet_nil
#check @kernel_differential_coordinates
#check @zeta_spatialPartial
#check @zeta_timePartial
#check @zeta_add
#check @zeta_unique_quasiperiod
#print axioms MathResearch.Fueter.E3_v2
-- Any real quaternion basis gives an admissible lattice, without integrality restrictions.
example (b : Module.Basis (Fin 4) ℝ ℍ) :
    ∃! η : Submodule.span ℤ (Set.range b) →+ ℍ,
      ∀ w : Submodule.span ℤ (Set.range b), ∀ q : ℍ, q ∉ Submodule.span ℤ (Set.range b) →
        zeta (Submodule.span ℤ (Set.range b)) (q + (w : ℍ)) -
          zeta (Submodule.span ℤ (Set.range b)) q = η w :=
  zeta_unique_quasiperiod _
-- Both regularities are conclusions, with no regularity or convergence hypotheses.
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L] :
    TwoSidedRegularOn (zeta L) (L : Set ℍ)ᶜ := (E3_v2 L).2.2.2.2.1
-- The undifferentiated Taylor bracket, including the leading kernel, is absolutely summable.
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L] (q : ℍ) (hq : q ∉ L) :
    Summable (fun a : L => ‖zetaJet [] (a : ℍ) q‖) := (E3_v2 L).1 [] q hq
-- Arbitrary real multi-indices include time derivatives and have no upper order bound.
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]
    (α : Fin 4 → ℕ) (q : ℍ) (hq : q ∉ L) :
    (∑' a : L, multiIndexPartial α (zetaJet [] (a : ℍ)) q) = multiIndexPartial α (zeta L) q :=
  zeta_termwise_tsum L _ hq
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]
    (α : Fin 4 → ℕ) :
    HasSumLocallyUniformlyOn (fun a : L => multiIndexPartial α (zetaJet [] (a : ℍ)))
      (multiIndexPartial α (zeta L)) (L : Set ℍ)ᶜ := zeta_termwise_locallyUniform L _
-- The nonzero zeroth jet is the literal E-C2 bracket, not a separately summed subtraction.
example (a q : ℍ) (ha : a ≠ 0) :
    zetaJet [] a q = kernel (a + q) - kernel a - fderiv ℝ kernel a q := by
  simpa [add_comm] using zetaJet_nil a q ha
