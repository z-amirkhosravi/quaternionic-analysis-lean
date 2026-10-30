import MathResearch
open scoped Quaternion Topology BigOperators
open MathResearch.Fueter
#check @N2_v1
#check @N3_v1
#print spatialMultiIndex
#print higherKernel
#print eisensteinCoefficient
#print higherLatticeSum
#print higherElliptic
#print axioms MathResearch.Fueter.N2_v1
#print axioms MathResearch.Fueter.N3_v1
-- Every real basis of quaternion space yields an admissible lattice, not just the cubic lattice.
example (b : Module.Basis (Fin 4) ℝ ℍ) (ν : Fin 3 → ℕ)
    (hν : 2 ≤ ∑ j, ν j) (heven : Even (∑ j, ν j)) :
    eisensteinCoefficient (Submodule.span ℤ (Set.range b)) ν = 0 :=
  N3_v1 _ ν hν heven
-- In particular the hypotheses are inhabited by the standard quaternion basis and order two.
example : eisensteinCoefficient (Submodule.span ℤ (Set.range coordinateBasis)) ![2, 0, 0] = 0 := by
  apply N3_v1
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]
