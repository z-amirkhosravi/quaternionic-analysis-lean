module
public import MathResearch.Hardy.KelvinIntertwining
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-! OPEN compact spectral inputs, separately exposed.

Peter–Weyl and Clebsch–Gordan yield the two spinor K-type strings. The local
Fueter polynomial calculation identifies the positive string with H+.
This module states the precise output needed by the research deduction;
it does not claim proofs of those background theorems or their specialization.
In particular, these are not consequences of merely knowing dimensions. -/
@[expose] public section
noncomputable section
open scoped TensorProduct
namespace MathResearch.Hardy
open Spinor

abbrev PositiveCompactType (m : ℕ) := BinaryForm m ⊗[ℂ] BinaryForm (m+1)

def positiveCompactAction (m : ℕ) (k : CompactPair) :
    PositiveCompactType m →ₗ[ℂ] PositiveCompactType m :=
  TensorProduct.map (polynomialRepresentation m (quaternionMatrix k.1))
    (polynomialRepresentation (m+1) (quaternionMatrix k.2))

/-- Orthogonal intertwiners, completeness in full boundary L², and the
identification with the independently defined closure of regular polynomials. -/
structure SpinorCompactExpansionData (area : BoundaryAreaFormula) where
  positive : ∀ m : ℕ, PositiveCompactType m →ₗᵢ[ℂ] BoundaryL2
  equivariant : ∀ m k v, boundaryRepresentation area (compactSp11 k) (positive m v) =
    positive m (positiveCompactAction m k v)
  pairwise_orthogonal : ∀ m n, m ≠ n → ∀ v w,
    inner ℂ (positive m v) (positive n w) = 0
  cross_orthogonal : ∀ m n v w, inner ℂ (positive m v) (kelvinUnitary (positive n w)) = 0
  hardy_span : (⨆ m, LinearMap.range (positive m).toLinearMap).topologicalClosure = hardyBoundary
  boundary_span : ((⨆ m, LinearMap.range (positive m).toLinearMap) ⊔
    (⨆ m, LinearMap.range (positive m).toLinearMap).map kelvinUnitary.toLinearEquiv.toLinearMap).topologicalClosure = ⊤

end MathResearch.Hardy
