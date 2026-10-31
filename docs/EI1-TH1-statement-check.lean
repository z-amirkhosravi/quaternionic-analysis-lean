import MathResearch
open scoped Quaternion Topology BigOperators ContDiff
open MathResearch.Fueter MeasureTheory Set
#check @EI1_v1
#check @TH1_v1
#print realCoord
#print polyEval
#print kernelNumerator
#print harmonicNumerator
#print numeratorCoefficient
#print harmonicTheta
#check @polyEval_pderiv
#check @polyEval_laplacian
#check @numeratorJet_represents
#check @kernelNumerator_recurrence
#check @harmonicTheta_mellin
#print axioms MathResearch.Fueter.EI1_v1
#print axioms MathResearch.Fueter.TH1_v1

-- The numerator for a first spatial derivative has the expected sign and factor 4.
example (q : ℍ) : polyEval (kernelNumerator (Pi.single 0 1) 1) q =
    4 * (realCoord 1 q) ^ 2 - Quaternion.normSq q := by
  simp [kernelNumerator, spatialDerivativeList, numeratorJet, conjugatePoly, numeratorStep,
    polyEval, normSqPoly, coordinateBasis, QuaternionAlgebra.coe_basisOneIJK_repr,
    Quaternion.normSq_def, Fin.sum_univ_succ]
  ring

-- EI1 represents the actual quaternionic derivative, with the singular point excluded.
example (ν : Fin 3 → ℕ) (q : ℍ) (hq : q ≠ 0) :
    higherKernel ν q = (Quaternion.normSq q ^ ((∑ i, ν i) + 2))⁻¹ • harmonicNumerator ν q :=
  EI1_v1.2.1 ν q hq

-- Harmonicity uses mathlib's actual Euclidean Laplacian on all of quaternion space.
example (ν : Fin 3 → ℕ) (k : Fin 4) :
    InnerProductSpace.HarmonicOnNhd (polyEval (kernelNumerator ν k)) Set.univ :=
  (EI1_v1.1 ν k).2

-- Every spatial direction is available for every multi-index, including mixed derivatives.
example (ν : Fin 3 → ℕ) (j : Fin 3) (k : Fin 4) :
    kernelNumerator (ν + Pi.single j 1) k =
      numeratorStep (∑ i, ν i) j.succ (kernelNumerator ν k) := kernelNumerator_recurrence ν j k

-- At the smallest written order, any real basis gives an admissible full Euclidean lattice.
-- There is no integrality/evenness assumption on its Gram matrix, nor a convergence premise.
example (b : Module.Basis (Fin 4) ℝ ℍ) (k : Fin 4) :
    numeratorCoefficient (Submodule.span ℤ (Set.range b)) ![3, 0, 0] k =
      Real.pi ^ 5 / Real.Gamma 5 * ∫ t : ℝ in Ioi 0,
        t ^ 4 * harmonicTheta (Submodule.span ℤ (Set.range b)) ![3, 0, 0] k t := by
  have h := TH1_v1 (Submodule.span ℤ (Set.range b)) ![3, 0, 0] k
    (by simpa [Fin.sum_univ_succ] using (show Odd (3 : ℕ) from ⟨1, rfl⟩))
    (by norm_num [Fin.sum_univ_succ])
  have he := h.2.2.2.2.2
  norm_num [Fin.sum_univ_succ] at he ⊢
  exact he

-- The scalar quantity in the Mellin formula is the existing Eisenstein coefficient's component.
example (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]
    (ν : Fin 3 → ℕ) (k : Fin 4) (hν : 2 ≤ ∑ i, ν i) :
    numeratorCoefficient L ν k = realCoord k (eisensteinCoefficient L ν) :=
  numeratorCoefficient_eq_component L ν k hν

-- TH-D1 has exp(2πiτQ), with Q=N/2. At τ=it this is the exact real exponential used here.
example (t N : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((t : ℂ) * Complex.I) * ((N : ℂ) / 2)) =
      (Real.exp (-Real.pi * t * N) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  calc
    _ = -(Real.pi : ℂ) * (t : ℂ) * (N : ℂ) := by
      calc
        _ = (Real.pi : ℂ) * (t : ℂ) * (N : ℂ) * Complex.I ^ 2 := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    _ = _ := rfl
