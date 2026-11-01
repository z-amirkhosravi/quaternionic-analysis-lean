module
public import MathResearch.Analysis.SpinorCompactExpansion

/-! EXTERNAL representation-theoretic recognition theorem.

The representation `π₁` is supplied by the external classification, not defined
as “irreducible and non-square-integrable”. The hypothesis below is a precise
unitary-equivalence recognition statement for the positive K-type summand of
the actual boundary representation. It applies to any Hilbert realization,
not just the Hardy model.

Sources: Liu–Zhang, printed p.2996 after Theorem 3.11; Camporesi–Pedon,
Theorem 3.2 final step, printed p.252 (citing Thieleker, Theorem 6).
The bridge identifying our boundary formula with their normalized induced
model must also be supplied to justify this hypothesis. The fixed-point weight
is checked separately in Hardy/Normalization; full induction is not encoded.

No general Lean definition of a limit of discrete series, Fell topology, or
the cited classification is asserted here. Consequently the research result
is a CONDITIONAL realization in an externally classified π₁, not an
unconditional kernel proof of that classification. There is no axiom or instance.
-/
@[expose] public section
noncomputable section
namespace MathResearch.Hardy
open Spinor

/-- External positive-spinor recognition, including the coordinate/convention
bridge to the independently specified boundary representation. -/
def SpinorEndpointClassification (area : BoundaryAreaFormula)
    (kt : SpinorCompactExpansionData area)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π₁ : Sp11 →* (E ≃ₗᵢ[ℂ] E)) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ (ρ : Sp11 →* (H ≃ₗᵢ[ℂ] H)) (j : H →ₗᵢ[ℂ] BoundaryL2),
      TopologicallyIrreducible ρ →
      (∀ g x, j (ρ g x) = boundaryRepresentation area g (j x)) →
      LinearMap.range j.toLinearMap =
        (⨆ m, LinearMap.range (kt.positive m).toLinearMap).topologicalClosure →
      ∃ e : H ≃ₗᵢ[ℂ] E, ∀ g x, e (ρ g x) = π₁ g (e x)

end MathResearch.Hardy
