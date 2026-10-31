import MathResearch
noncomputable section
set_option pp.funBinderTypes true
open scoped Quaternion Topology BigOperators ContDiff
open MathResearch.Fueter

#check @EI7_v1
#print UnitQuaternion
#print QuaternionSpinPair
#print QuaternionSO4
#print quaternionIsometryDet
#print kernelDerivativeSpace
#print smoothPuncturedSpace
#print CoefficientFunctional
#print latticeCoefficientFunctional
#check @kernelDerivativeSpace_eq_real_span
#check @quaternionSpinCover_surjective
#check @quaternionRotation_kernel
#check @coefficientSigmaLinear_mul
#check @coefficientSO4Representation_lift
#check @coefficient_SO4_covariance
#print axioms MathResearch.Fueter.EI7_v1
#print axioms MathResearch.Fueter.quaternionSpinCover_surjective

-- The standard orthonormal basis identifies this space with Euclidean R^4.
example : Orthonormal ℝ coordinateBasis := coordinateBasis_orthonormal

-- Mathlib's unitary condition is exactly the usual unit-norm condition here.
example (q : ℍ) : q ∈ unitary ℍ ↔ ‖q‖ = 1 := by
  constructor
  · intro h
    exact unitQuaternion_norm ⟨q, h⟩
  · intro h
    constructor
    · rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, h, one_mul, Quaternion.coe_one]
    · rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, h, one_mul, Quaternion.coe_one]

-- Right multiplication really is the opposite-ring scalar action.
example (c : ℍ) (f : SmoothPunctured) (q : ℍ) :
    (MulOpposite.op c • f) q = f q * c := rfl

-- Spatial generators are the existing real Fréchet derivatives off zero.
example (ν : Fin 3 → ℕ) (q : ℍ) (hq : q ≠ 0) :
    smoothHigherKernel ν q = multiIndexPartial (spatialMultiIndex ν) kernel q :=
  smoothHigherKernel_apply ν hq

-- All four real directions, including arbitrary mixed time derivatives, give the same span.
example (r : ℕ) : kernelDerivativeSpace r =
    Submodule.span ℍᵐᵒᵖ (Set.range (fun l : {l : List (Fin 4) // l.length = r} =>
      smoothKernelPartial l)) := kernelDerivativeSpace_eq_real_span r

-- The input action is b f(a^{-1} q b), with factors on the specified sides.
example (r : ℕ) (a b : UnitQuaternion) (f : kernelDerivativeSpace r) (q : ℍ) :
    (kernelRho r (a, b) f : SmoothPunctured) q =
      (b : ℍ) * (f : SmoothPunctured) (star (a : ℍ) * q * (b : ℍ)) := by
  change smoothRho (a, b) (f : SmoothPunctured) q = _
  simp only [smoothRho_apply, quaternionRotation_apply, Prod.fst_inv, Prod.snd_inv,
    unitQuaternion_coe_inv, star_star]

-- The formula uses inverse precomposition, not forward precomposition.
example (r : ℕ) (k : QuaternionSpinPair) (α : CoefficientFunctional r)
    (f : kernelDerivativeSpace r) :
    coefficientSigma r k α f = (k.2 : ℍ) * α ((kernelRho r k).symm f) := by
  change (k.2 : ℍ) * α (kernelRho r k⁻¹ f) = _
  rw [kernelRho_inv]

-- SO(4) consists of actual determinant-one isometries, with no covering premise.
example (e : QuaternionSO4) : LinearEquiv.det e.val.toLinearEquiv = 1 := e.property
example (e : QuaternionSO4) : ∃ k : QuaternionSpinPair, quaternionSpinCover k = e :=
  quaternionSpinCover_surjective e

-- Both simultaneous minus signs cancel on the functional representation.
example (r : ℕ) (α : CoefficientFunctional r) : coefficientSigma r (-1, -1) α = α := by
  rw [coefficientSigma_central]
  rfl

-- These are mathlib representations on the real vector space of right-H-linear maps.
example (r : ℕ) : Representation ℝ QuaternionSO4 (CoefficientFunctional r) :=
  coefficientSO4Representation r
example (r : ℕ) (k l : QuaternionSpinPair) :
    coefficientSpinRepresentation r (k * l) =
      coefficientSpinRepresentation r k * coefficientSpinRepresentation r l := map_mul _ _ _

section Lattices
variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

-- The nonzero lattice index and the actual sum are visible.
example (r : ℕ) (hr : 1 < r) (f : kernelDerivativeSpace r) :
    latticeCoefficientFunctional L r hr f =
      ∑' w : {w : L // w ≠ 0}, (f : SmoothPunctured) (w.1 : ℍ) := rfl

-- The new functional specializes to the already verified Eisenstein coefficients.
example (ν : Fin 3 → ℕ) (hν : 2 ≤ ∑ j, ν j) :
    latticeCoefficientFunctional L (∑ j, ν j) hν ⟨smoothHigherKernel ν, smoothHigherKernel_mem ν⟩ =
      eisensteinCoefficient L ν := latticeCoefficientFunctional_generator L ν hν

-- The lattice rotates forward as a L b^{-1}.
example (a b : UnitQuaternion) (q : ℍ) :
    q ∈ rotatedLattice L (quaternionRotation (a, b)) ↔
      ∃ x ∈ L, (a : ℍ) * x * star (b : ℍ) = q := mem_rotatedLattice L _ q

-- Arbitrary full lattices, every r>1, and every actual rotation are covered.
example (r : ℕ) (hr : 1 < r) (e : QuaternionSO4) :
    latticeCoefficientFunctional (rotatedLattice L e.val) r hr =
      coefficientSO4Representation r e (latticeCoefficientFunctional L r hr) :=
  (EI7_v1 L r hr).2.2.2.2 e
end Lattices
