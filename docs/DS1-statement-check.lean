import MathResearch
noncomputable section
open scoped BigOperators Quaternion
open MvPolynomial MathResearch.Spinor
set_option pp.funBinderTypes true

#check DS1_v1
#check spinorIsometry
#check binaryForm_norm_sq
#check formRow_norm_sq
#check quaternionCoefficients_bijective
#check pack_smul
#check normalizedGradient_quaternionCoefficients
#check derivative_norm_sq
#check finrank_compatibleRow
#print axioms DS1_v1

-- V_n is mathlib's actual homogeneous polynomial submodule.
example (n : ℕ) : BinaryForm n = homogeneousSubmodule (Fin 2) ℂ n := rfl

-- W consists precisely of pairs whose actual polynomial partials agree.
example (m : ℕ) (h : FormRow m) : h ∈ compatibleRows m ↔
    pderiv 1 (h 0 : MvPolynomial (Fin 2) ℂ) =
      pderiv 0 (h 1 : MvPolynomial (Fin 2) ℂ) := Iff.rfl

-- The binomial coefficient norm is specified independently of the gradient.
example (n : ℕ) (p : BinaryForm n) :
    ‖p‖ ^ 2 = ∑ k, ‖(p : MvPolynomial (Fin 2) ℂ).coeff (exponent n k)‖ ^ 2 /
      (n.choose k : ℝ) := binaryForm_norm_sq n p

-- A-jB identifies (A,B) with (Re A, Im A, -Re B, Im B).
example (a b : ℂ) : pack a b = (a : ℍ) - (⟨0, 0, 1, 0⟩ : ℍ) * (b : ℍ) := rfl
example : pack 0 1 = (⟨0, 0, -1, 0⟩ : ℍ) := by simp [pack_components]
example : pack 0 Complex.I = (⟨0, 0, 0, 1⟩ : ℍ) := by simp [pack_components]
example (z a b : ℂ) : pack (z * a) (z * b) = pack a b * (z : ℍ) := pack_smul z a b

-- Both directions of DS1 use actual derivatives and multiplication by X,Y.
example (m : ℕ) (p : BinaryForm (m + 1)) (i : Fin 2) :
    ((spinorIsometry m p).val i : MvPolynomial (Fin 2) ℂ) =
      (m + 1 : ℂ)⁻¹ • pderiv i (p : MvPolynomial (Fin 2) ℂ) := rfl
example (m : ℕ) (h : CompatibleRow m) :
    ((spinorIsometry m).symm h : MvPolynomial (Fin 2) ℂ) =
      X 0 * (h.val 0 : MvPolynomial (Fin 2) ℂ) +
      X 1 * (h.val 1 : MvPolynomial (Fin 2) ℂ) := rfl

-- The endpoint n=1 is included, not merely n≥2.
example : Module.finrank ℂ (CompatibleRow 0) = 2 := finrank_compatibleRow 0
example (p : BinaryForm 1) : ‖spinorIsometry 0 p‖ = ‖p‖ := (spinorIsometry 0).norm_map p
example (p : BinaryForm 1) (i : Fin 2) :
    ((spinorIsometry 0 p).val i : MvPolynomial (Fin 2) ℂ) =
      pderiv i (p : MvPolynomial (Fin 2) ℂ) := by
  simp [normalizedGradient, derivative]

-- Degree-two middle monomial: the squared norm is 1/2, not 1.
example : ‖(coefficientEquiv 2).symm ![0, 1, 0]‖ ^ 2 = (1 / 2 : ℝ) := by
  have hc : coefficients 2 ((coefficientEquiv 2).symm ![0, 1, 0]) = ![0, 1, 0] :=
    (coefficientEquiv 2).apply_symm_apply _
  rw [binaryForm_norm_sq, hc]
  norm_num [Fin.sum_univ_succ]

-- No unproved representation-theoretic input appears in the signature.
example (n : ℕ) (hn : 1 ≤ n) : Nonempty (BinaryForm n ≃ₗᵢ[ℂ] CompatibleRow (n - 1)) :=
  ⟨(DS1_v1 n hn).choose⟩
