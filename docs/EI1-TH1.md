# EI1 and TH1/v1: harmonic numerators and their Mellin formula

The targets are **EI1/v1** in *Lattice Eisenstein series and representations* and
**TH1/v1** in *Harmonic theta series and special L-values*. The [source snapshot](EI1-TH1-source.json)
retains the complete accepted articles, convention source, revision and hashes.
Development starts from the independently pinned E4–E6 delivery.

## Definitions and correspondence

| Written object | Lean counterpart |
| --- | --- |
| Quaternion q and coordinates t,x,y,z | Mathlib's real quaternion type `ℍ`; the existing `coordinateBasis` is `(1,i,j,k)`. `realCoord k` is its continuous real component projection, for `k : Fin 4`. |
| N(q)=|q|² | The existing mathlib `Quaternion.normSq q`. The polynomial `normSqPoly = ∑ i : Fin 4, X i ^ 2` evaluates to it by `polyEval_normSq`. |
| Quaternion-valued polynomial Hν | `kernelNumerator ν : Fin 4 → MvPolynomial (Fin 4) ℝ` stores four ordinary real polynomials. `harmonicNumerator ν q` assembles their values in the quaternion basis. `harmonicNumerator_component` proves the component correspondence. |
| Polynomial evaluation | `polyEval P q = MvPolynomial.eval (coordinateBasis.repr q) P`. |
| Spatial multi-index and order r | The unchanged `ν : Fin 3 → ℕ` and `∑ i, ν i`. The existing `spatialDerivativeList` represents the written derivative order; `j.succ : Fin 4` is spatial direction j+1. |
| Homogeneous of degree r+1 | Mathlib's `MvPolynomial.IsHomogeneous ((∑ i, ν i) + 1)`. This permits a component to be the zero polynomial, as the mathematical statement requires. |
| Each component is harmonic | Mathlib's `InnerProductSpace.HarmonicOnNhd (polyEval (kernelNumerator ν k)) Set.univ`. This asserts twice continuous differentiability and vanishing of the actual Euclidean Laplacian in a neighborhood of every point. |
| ∂j Hν | Mathlib's polynomial `pderiv j.succ`. `polyEval_pderiv` proves that evaluation agrees with the real Fréchet derivative in `coordinateBasis j.succ`. |
| Gν(q)=Hν(q)/N(q)^(r+2) | EI1 equates the **existing** `higherKernel ν q` with the real scalar multiple `(Quaternion.normSq q ^ (r+2))⁻¹ • harmonicNumerator ν q`, for every q≠0. |
| Full Euclidean lattice L | The unchanged `L : Submodule ℤ ℍ`, `[DiscreteTopology L]`, `[IsZLattice ℝ L]`. An arbitrary real quaternion basis supplies these instances for its integer span. |
| Eν,H(L) | `numeratorCoefficient L ν k`, the literal scalar sum of H/N^(r+2) over nonzero lattice points. `numeratorCoefficient_eq_component` proves that it is `realCoord k (eisensteinCoefficient L ν)`. |
| θL,H(it) | `harmonicTheta L ν k t = ∑' l : L, polyEval (kernelNumerator ν k) l * Real.exp (-Real.pi * t * Quaternion.normSq l)`. The zero term is included and proved to vanish. This uses the written normalization N=2Q, so exp(2πi(it)Q)=exp(−πtN). |
| Integral from 0 to ∞ | Mathlib's Lebesgue integral over `Set.Ioi 0`; its absolute integrability is a separate proved conclusion. |

The construction starts with the four components of quaternionic conjugation:

```lean
def conjugatePoly (k : Fin 4) : RealPoly4 := if k = 0 then X k else -X k

def numeratorStep (r : ℕ) (j : Fin 4) (P : RealPoly4) : RealPoly4 :=
  normSqPoly * pderiv j P - C (2 * ((r : ℝ) + 2)) * (X j * P)

def numeratorJet : List (Fin 4) → Fin 4 → RealPoly4
  | [], k => conjugatePoly k
  | j :: l, k => numeratorStep l.length j (numeratorJet l k)

def kernelNumerator (ν : Fin 3 → ℕ) (k : Fin 4) : RealPoly4 :=
  numeratorJet (spatialDerivativeList ν) k
```

`numeratorStep_comm` and `numeratorJet_perm` prove order independence algebraically.
Thus the recurrence holds for every multi-index and **every** spatial direction,
not just an insertion compatible with one chosen ordering. The auxiliary
`numeratorJet_represents` covers arbitrary ordered real derivatives, including
the time direction. The final EI1 statement uses the written spatial indexing.

## Exact statements

Both declarations are in namespace `MathResearch.Fueter`:

```lean
theorem EI1_v1 :
    (∀ (ν : Fin 3 → ℕ) (k : Fin 4),
      (kernelNumerator ν k).IsHomogeneous ((∑ i, ν i) + 1) ∧
      InnerProductSpace.HarmonicOnNhd (polyEval (kernelNumerator ν k)) Set.univ) ∧
    (∀ (ν : Fin 3 → ℕ) (q : ℍ), q ≠ 0 →
      higherKernel ν q = (Quaternion.normSq q ^ ((∑ i, ν i) + 2))⁻¹ • harmonicNumerator ν q) ∧
    (∀ q : ℍ, harmonicNumerator 0 q = star q) ∧
    (∀ (ν : Fin 3 → ℕ) (j : Fin 3) (k : Fin 4),
      kernelNumerator (ν + Pi.single j 1) k =
        normSqPoly * pderiv j.succ (kernelNumerator ν k) -
          C (2 * (((∑ i, ν i) : ℕ) : ℝ) + 4) * (X j.succ * kernelNumerator ν k))
```

The last coefficient `2*r+4` is `2*(r+2)`. The initial value, polynomial
homogeneity, analytic harmonicity, representation of actual kernel derivatives,
and recurrence are all conclusions; none is assumed.

TH1 has the standing lattice parameters
`(L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]`:

```lean
theorem TH1_v1 (ν : Fin 3 → ℕ) (k : Fin 4) (_hodd : Odd (∑ i, ν i))
    (hν : 3 ≤ ∑ i, ν i) :
    (∀ t : ℝ, 0 < t → Summable (fun l : L =>
      polyEval (kernelNumerator ν k) (l : ℍ) * exp (-Real.pi * t * Quaternion.normSq (l : ℍ)))) ∧
    Summable (fun l : {l : L // l ≠ 0} => |polyEval (kernelNumerator ν k) (l.1 : ℍ)| /
      Quaternion.normSq (l.1 : ℍ) ^ ((∑ i, ν i) + 2)) ∧
    Summable (fun l : {l : L // l ≠ 0} => ∫ t : ℝ in Ioi 0,
      ‖t ^ ((∑ i, ν i) + 1) * (polyEval (kernelNumerator ν k) (l.1 : ℍ) *
        exp (-Real.pi * t * Quaternion.normSq (l.1 : ℍ)))‖) ∧
    IntegrableOn (fun t : ℝ => t ^ ((∑ i, ν i) + 1) * harmonicTheta L ν k t) (Ioi 0) ∧
    numeratorCoefficient L ν k = realCoord k (eisensteinCoefficient L ν) ∧
    numeratorCoefficient L ν k = Real.pi ^ ((∑ i, ν i) + 2) / Gamma (((∑ i, ν i) : ℕ) + 2) *
      ∫ t : ℝ in Ioi 0, t ^ ((∑ i, ν i) + 1) * harmonicTheta L ν k t
```

The six conclusions are theta summability for every positive t; absolute lattice
coefficient convergence; summability of the integrals of absolute values;
integrability of the weighted theta function; agreement with the existing
Eisenstein coefficient; and the Mellin formula with π^(r+2)/Γ(r+2).
`_hodd` retains the written odd-order assumption. The proof actually works for
all orders at least two, as stated separately in `harmonicTheta_mellin` and its
convergence lemmas. No evenness or integrality of the lattice Gram matrix is
assumed. This delivery concerns the imaginary-axis theta series and TH1's
Mellin identity; it does not establish theta modularity.

These small definition comparisons and exact signatures are available for any
reader to examine. They carry no visitor approval input or tracked approval
state. Correspondence with the written mathematics remains distinct from the
Lean proof check.

## Proof and mathlib reuse

- [HarmonicPolynomial.lean](../MathResearch/Fueter/HarmonicPolynomial.lean)
  uses mathlib's real multivariate polynomials, partial derivations, homogeneous
  polynomials and Euler identity. The product rules give
  Δ(N∂jH)=(4r+8)∂jH and Δ(xjH)=2∂jH when H has degree r+1 and is harmonic.
  These terms cancel in the numerator recurrence.
- [PolynomialCalculus.lean](../MathResearch/Fueter/PolynomialCalculus.lean)
  proves the evaluation/Fréchet derivative bridge, smoothness of evaluation,
  and equality between the polynomial Laplacian and mathlib's Euclidean
  Laplacian. It equips the existing quaternion basis with mathlib's
  `OrthonormalBasis` structure.
- [KernelNumerator.lean](../MathResearch/Fueter/KernelNumerator.lean)
  differentiates the polynomial-over-norm-square identity on the punctured
  domain. All equality and derivative steps refer to the unchanged kernel and
  derivative definitions from F1/F2.
- [RealMellin.lean](../MathResearch/Fueter/RealMellin.lean) specializes
  mathlib's Gamma integral and Gaussian integrability results to natural
  powers. Mathlib's exponential series bound proves positive-time theta
  convergence. `hasSum_integral_of_summable_integral_norm` proves interchange;
  a measurable-sum and nonnegative-integral argument also proves integrability
  of the resulting sum.
- [HarmonicTheta.lean](../MathResearch/Fueter/HarmonicTheta.lean) projects N2's
  already proved absolute quaternionic coefficient bound through continuous
  real component maps, substitutes EI1 and applies the real Mellin lemmas.
  It proves the exact scalar coefficient bridge and removes the vanishing
  zero theta term. The normalization is derived from Γ(s)/(πN)^s with s=r+2.

All earlier mathematical source files and dependency pins are preserved.
There are no additional axioms, convergence assumptions or unproved analytic
premises in EI1 or TH1.

## Reproduction and evidence

```sh
python3 scripts/verify.py --clean-local
bash scripts/lake.sh env lean -DwarningAsError=true docs/EI1-TH1-statement-check.lean
```

The statement check prints both signatures and the relevant definitions, checks
the sign and coefficient of an explicit first derivative, extracts EI1's actual
kernel identity and harmonicity, checks the arbitrary-direction recurrence,
and instantiates TH1 at order three for the integer span of an arbitrary real
quaternion basis. It also checks the scalar coefficient bridge.

VERIFICATION_RECORD_PENDING

The verifier rebuilds all local Lean modules and audits every local declaration,
including private and generated ones. It permits only `propext`,
`Classical.choice` and `Quot.sound`, and treats warnings as errors. The pinned
upstream mathlib release artifacts are retained; this is not a full mathlib
rebuild or an independent proof-kernel run. Lean 4.35.0 and mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` remain pinned.

This separate `codex/ei1-th1` worktree preserves all previous checkouts and wiki
exports. Wiki integration and publication are separate actions.
