# EI7/v1: rotation covariance of coefficient functionals

`MathResearch.Fueter.EI7_v1` verifies the published EI7/v1 in
`lattice-eisenstein-series.md`. The exact accepted article and its dependencies
are retained in [EI7-source.json](EI7-source.json), from Math Research revision
`4ee36d2703b5fe5730115d6535e53fd8c678505f`.

For every full Euclidean quaternionic lattice L and every natural order r>1,
the theorem proves invariance of U under ρ, absolute convergence on all of U,
α_(aLb⁻¹)=σ(a,b)α_L, equality of the spin representation with its SO(4) lift,
and covariance under every element of SO(4). Right quaternion linearity of
α_L and real linearity and group laws of σ are part of the types of the
constructed maps and mathlib `Representation`s. There is no assumed
convergence, invariance, covering theorem, or descent premise.

The main statement is in
[RotationCovariance.lean](../MathResearch/Fueter/RotationCovariance.lean).
[EI7-statement-check.lean](EI7-statement-check.lean) prints its exact signature
and checks the small definition comparisons below. These comparisons are
available for any reader to examine; there is no visitor approval state.

## Definition comparisons

| Written object | Lean object | Meaning to inspect |
| --- | --- | --- |
| Unit quaternion | `UnitQuaternion := unitary ℍ` | Mathlib's quaternions and unitary group; `unitQuaternion_norm` proves norm one. |
| Spin(4) pair (a,b) | `QuaternionSpinPair` | Product of two unit quaternion groups. |
| Forward rotation | `quaternionRotation (a,b)` | The real linear isometry q ↦ a q star(b); star(b)=b⁻¹ for unit b. |
| SO(4) | `QuaternionSO4` | Kernel of the determinant homomorphism on real linear isometries of ℍ. The existing orthonormal basis `(1,i,j,k)` identifies this with ordinary Euclidean SO(4). |
| Functions on ℍ∖{0} | `SmoothPunctured` | Smooth functions off zero, represented by their zero extension. `SmoothPunctured.ext` says equality is determined entirely off zero. No derivative at the singular point is used. |
| Right multiplication f c | `MulOpposite.op c • f` | Pointwise f(q)c, using mathlib's opposite-ring module. |
| Order-ν kernel derivative | `smoothHigherKernel ν` | The existing `higherKernel ν`, hence actual iterated real Fréchet derivatives, restricted off zero. |
| U_(−r−3) | `kernelDerivativeSpace r` | Right quaternion span of generators with total spatial order r. `kernelDerivativeSpace_eq_real_span` proves equality with the span of every ordered length-r real derivative list, including time derivatives. |
| ρ(a,b) | `kernelRho r (a,b)` | Right quaternion linear equivalence f(q) ↦ b f(star(a) q b). |
| Right-H-linear functionals | `CoefficientFunctional r` | Mathlib linear maps from U to ℍ over the opposite quaternion ring. This space has its ordinary real vector-space structure. |
| α_L | `latticeCoefficientFunctional L r hr` | Actual `tsum` over nonzero lattice points. Absolute convergence is separately proved for every f∈U. Generator values equal existing `eisensteinCoefficient`s. |
| σ(a,b)α | `coefficientSigma r (a,b) α` | f ↦ b α(ρ(a,b)⁻¹ f). Both output multiplication and inverse precomposition are explicit. |
| Real representations | `coefficientSpinRepresentation`, `coefficientSO4Representation` | Mathlib `Representation ℝ` on the same functional space; their equality along the covering map is proved. |
| aLb⁻¹ | `rotatedLattice L (quaternionRotation (a,b))` | Mathlib lattice transport. `mem_rotatedLattice` proves it is exactly the image of L. |

## Proof dependencies

[QuaternionRotations.lean](../MathResearch/Fueter/QuaternionRotations.lean)
constructs rotations using mathlib's unitary groups and linear isometries.
Determinants of left and right quaternion multiplication are computed in the
standard basis. Mathlib's Cartan–Dieudonné theorem, together with the explicit
quaternion formula for a reflection, proves that every determinant-one
isometry has a spin lift. The covering kernel is proved to be exactly
`(1,1)` and `(-1,-1)`.

[PuncturedSmooth.lean](../MathResearch/Fueter/PuncturedSmooth.lean) and
[KernelRotationAction.lean](../MathResearch/Fueter/KernelRotationAction.lean)
use mathlib's Fréchet chain rule, F1 regularity, and the earlier commutation of
smooth partial derivatives. Right regularity of the kernel derivatives
eliminates time derivatives with coefficients on the right. Differentiation
is right quaternion linear, so this extends to their span. The proof does
not assume that right regularity itself is preserved by arbitrary right
quaternion multiplication. Kernel covariance and the chain rule then prove
invariance of this exact span under ρ.

[CoefficientRepresentation.lean](../MathResearch/Fueter/CoefficientRepresentation.lean)
checks the forward group law, including the reverse order of inverse
precomposition. At `(-1,-1)`, ρ=-id and the output factor is -1, so σ=id.
Mathlib's `MonoidHom.liftOfSurjective` descends this action to the actual SO(4)
using the covering and kernel results proved here.

[RotationCovariance.lean](../MathResearch/Fueter/RotationCovariance.lean)
extends N2 absolute convergence to finite right-linear combinations and
constructs α_L as a linear map. Mathlib's lattice transport supplies the
bijection of nonzero indices. Reindexing gives the forward lattice covariance.
No arithmetic condition, integrality, symmetry, or fixed basis of L is assumed.

## Reproduce the check

```sh
python3 scripts/verify.py --clean-local
bash scripts/lake.sh env lean -DwarningAsError=true docs/EI7-statement-check.lean
```

The retained run passed: **30 local modules rebuilt, 629 declarations audited,
zero warnings**. Every local declaration, including private and generated
helpers, uses only the allowed standard axioms. The checked source revision is
`77bdcc565295c577b383af0ba3f0c0f90e791967`. The post-clean statement check also
passed; it includes equivalence between unitary and unit-norm quaternions.

The retained clean-build/axiom audit is
[evidence/EI7-v1-2026-10-31.json](../evidence/EI7-v1-2026-10-31.json), with the
printed statements and definition comparisons in
[evidence/EI7-statement-check-2026-10-31.json](../evidence/EI7-statement-check-2026-10-31.json).
The checker accepts only `propext`, `Classical.choice`, and `Quot.sound` and
treats warnings as errors. The pinned Lean 4.35.0 and mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` are unchanged. Upstream mathlib cache
artifacts are retained; the check rebuilds local proofs and uses Lean's kernel.

This branch extends the EI1/TH1 delivery without changing any earlier proof
module. It does not publish a wiki panel or alter earlier wiki packages.
