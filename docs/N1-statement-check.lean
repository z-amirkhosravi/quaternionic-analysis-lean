import MathResearch
open scoped Quaternion Topology BigOperators ContDiff
open MathResearch.Fueter
#check @N1_v2
#check @N1_coefficient_summable
#print ellipticRegularPart
#print ellipticRegularPartDomain
#print spatialDerivativeList
#print spatialMultiIndex
#print higherKernel
#print eisensteinCoefficient
#check @ellipticRegularPart_eq
#check @ellipticRegularPart_regular
#check @ellipticRegularPart_coefficient
#check @ellipticRegularPart_extension_eqOn
#print axioms MathResearch.Fueter.N1_v2
-- An arbitrary real basis, not only the cubic lattice, gives an admissible example.
example (b : Module.Basis (Fin 4) ℝ ℍ) (j : Fin 3) (μ : Fin 3 → ℕ)
    (hμ : 1 ≤ ∑ i, μ i) :
    multiIndexPartial (spatialMultiIndex μ)
      (ellipticRegularPart (Submodule.span ℤ (Set.range b)) j) 0 =
      eisensteinCoefficient (Submodule.span ℤ (Set.range b)) (μ + Pi.single j 1) := by
  apply N1_v2 _ j (isOpen_ellipticRegularPartDomain _) (zero_mem_ellipticRegularPartDomain _)
    (ellipticRegularPart_regular _ j).1
  · exact fun q _ _ => ellipticRegularPart_eq_sub _ j q
  · exact hμ
-- The extension obtained from E1 itself satisfies N1, with no additional analytic assumption.
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]
    (j : Fin 3) (μ : Fin 3 → ℕ) (hμ : 1 ≤ ∑ i, μ i) :
    ∃ U : Set ℍ, IsOpen U ∧ (0 : ℍ) ∈ U ∧ ∃ h : ℍ → ℍ,
      TwoSidedRegularOn h U ∧
      (∀ q ∈ U, q ∉ L → h q = elliptic L j q - kernelSpatialPartial j q) ∧
      multiIndexPartial (spatialMultiIndex μ) h 0 = eisensteinCoefficient L (μ + Pi.single j 1) := by
  obtain ⟨U, hU, h0, h, hh, he⟩ := (E1_v2 L j).2.2.2.2 (0 : L)
  have he' : ∀ q ∈ U, q ∉ L → h q = elliptic L j q - kernelSpatialPartial j q := by
    simpa using he
  exact ⟨U, hU, h0, h, hh, he', N1_v2 L j hU h0 hh.1 he' μ hμ⟩
-- The first positive order is included, and its resulting coefficient has actual norm summability.
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L] (j : Fin 3) :
    Summable (fun a : {a : L // a ≠ 0} => ‖higherKernel (![1, 0, 0] + Pi.single j 1) (a.1 : ℍ)‖) :=
  N1_coefficient_summable L ![1, 0, 0] (by norm_num [Fin.sum_univ_succ]) j
