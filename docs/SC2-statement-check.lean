import MathResearch
noncomputable section
open scoped BigOperators Quaternion
open MvPolynomial MathResearch.Spinor
set_option pp.funBinderTypes true

#check polynomialRepresentation
#check generalLinearPolynomialRepresentation
#check polynomialRepresentation_hasDerivAt
#check quaternionPolynomialRepresentation_hasDerivAt
#check infinitesimal_commutator
#check quaternionMatrixHom
#check quaternionMatrix_pack
#check SC2_v1
#print axioms SC2_v1
#print axioms polynomialRepresentation_hasDerivAt

-- Exact column convention: the first argument is aX+cY, the second bX+dY.
example (M : Matrix2) (p : ComplexPoly2) : polynomialAction M p =
    aeval (fun i => C (M 0 i) * X 0 + C (M 1 i) * X 1) p := rfl
example (M : Matrix2) : polynomialAction M (X 0) = C (M 0 0) * X 0 + C (M 1 0) * X 1 := by
  simp [substitution]
example (M : Matrix2) : polynomialAction M (X 1) = C (M 0 1) * X 0 + C (M 1 1) * X 1 := by
  simp [substitution]

-- Ordinary representation order, not the opposite action.
example (n : ℕ) (M N : Matrix2) (p : BinaryForm n) :
    polynomialRepresentation n (M * N) p =
      polynomialRepresentation n M (polynomialRepresentation n N p) := by
  exact congrArg (fun L => L p) ((polynomialRepresentation n).map_mul M N)
example (n : ℕ) (M : Matrix.GeneralLinearGroup (Fin 2) ℂ) (p : BinaryForm n) :
    generalLinearPolynomialRepresentation n M⁻¹ (generalLinearPolynomialRepresentation n M p) = p := by
  simp

-- dτ(M) is the actual derivative at identity in DS1's weighted norm.
example (m : ℕ) (M : Matrix2) (p : BinaryForm (m + 1)) :
    HasDerivAt (fun t : ℂ => polynomialRepresentation (m + 1) (1 + t • M) p)
      (infinitesimalAction m M p) 0 := polynomialRepresentation_hasDerivAt m M p
example (M : Matrix2) (p : ComplexPoly2) : infinitesimal M p =
    (C (M 0 0) * X 0 + C (M 1 0) * X 1) * pderiv 0 p +
    (C (M 0 1) * X 0 + C (M 1 1) * X 1) * pderiv 1 p := rfl

-- The quaternion i,j,k matrices and their generator signs.
example : quaternionMatrix (⟨0, 1, 0, 0⟩ : ℍ) = !![Complex.I, 0; 0, -Complex.I] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quaternionMatrix]
example : quaternionMatrix quaternionJ = !![0, 1; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quaternionMatrix, quaternionJ]
example (p : ComplexPoly2) : infinitesimal (quaternionMatrix quaternionJ) p =
    -X 1 * pderiv 0 p + X 0 * pderiv 1 p := infinitesimal_j p
example (n : ℕ) (r : ℝ) (p : BinaryForm n) :
    infinitesimal (quaternionMatrix (r : ℍ)) p = ((n : ℂ) * r) • (p : ComplexPoly2) :=
  infinitesimal_real n r p
example (q : ℍ) (a b : ℂ) :
    pack (quaternionMatrix q 0 0 * a + quaternionMatrix q 0 1 * b)
      (quaternionMatrix q 1 0 * a + quaternionMatrix q 1 1 * b) = q * pack a b :=
  quaternionMatrix_pack q a b

-- T_n is the unnormalized p_X-jp_Y, encoded at every polynomial exponent.
example (p : ComplexPoly2) (d : Fin 2 →₀ ℕ) : polynomialFueterCoefficients p d =
    ((pderiv 0 p).coeff d : ℍ) - quaternionJ * ((pderiv 1 p).coeff d : ℍ) := rfl
example (q v : ℍ) : connectionCoefficient q v = (2 : ℝ)⁻¹ • (star v * q - star q * v) := rfl
example (q : ℍ) : connectionCoefficient q 1 = (⟨0, q.imI, q.imJ, q.imK⟩ : ℍ) := by
  ext <;> simp [connectionCoefficient] <;> ring

-- n=1 belongs to the theorem and gives factors 4 and 3 respectively.
example (q : ℍ) (p : BinaryForm 1) :
    (fun d => ∑ μ : Fin 4, MathResearch.Fueter.coordinateBasis μ *
      polynomialFueterCoefficients (infinitesimal (quaternionMatrix (star (MathResearch.Fueter.coordinateBasis μ) * q)) p) d) =
    (fun d => (4 : ℝ) • (q * polynomialFueterCoefficients p d)) := by
  convert (SC2_v1 1 (by decide) q p).1 using 1; norm_num
example (q : ℍ) (p : BinaryForm 1) :
    (fun d => ∑ μ : Fin 4, MathResearch.Fueter.coordinateBasis μ *
      polynomialFueterCoefficients (infinitesimal (quaternionMatrix (connectionCoefficient q (MathResearch.Fueter.coordinateBasis μ))) p) d) =
    (fun d => (3 : ℝ) • (q * polynomialFueterCoefficients p d)) := by
  convert (SC2_v1 1 (by decide) q p).2 using 1; norm_num

-- A concrete endpoint: q=1, p=X. The connection contribution is nonzero (3).
example : (∑ μ : Fin 4, MathResearch.Fueter.coordinateBasis μ *
    polynomialFueterCoefficients (infinitesimal (quaternionMatrix (connectionCoefficient 1 (MathResearch.Fueter.coordinateBasis μ))) (X 0)) 0) = 3 := by
  have h := congrFun (SC2_v1 1 (by decide) 1 ⟨X 0, isHomogeneous_X (R := ℂ) 0⟩).2 0
  convert h using 1
  norm_num [polynomialFueterCoefficients, pack, pderiv_X, Algebra.smul_def]
  ext <;> norm_num
