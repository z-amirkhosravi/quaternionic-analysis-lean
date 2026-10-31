# Polynomial representation and SC2/v1

This delivery formalizes the polynomial action used in the Sp(1,1) spinor model
and both projected connection identities. It extends DS1's actual homogeneous
polynomial spaces and weighted norms, using the same quaternion conventions.

For every homogeneous p∈V_n with n≥1 and every real quaternion q, SC2 states

\[
\sum_{v\in\{1,i,j,k\}} vT_n(d\tau_n(\bar vq)p)=2(n+1)qT_np,
\qquad
\sum_v vT_n(d\tau_n(C_v)p)=(n+2)qT_np,
\]

where T_np=p_X-jp_Y and C_v=(conj(v)q-conj(q)v)/2. The proof covers every degree
and every polynomial coefficient, without a finite-degree extrapolation or an
assumed connection theorem. The first formula extends the infinitesimal action
to all quaternions, including their real scalar part.

The [source snapshot](SC2-source.json) pins the exact wiki SC2/v1 formulation,
its conventions, and the relevant R060 calculation. The underlying analytic
connection interpretation remains the separate SC1 target.

## Small definition correspondences

All new declarations belong to `MathResearch.Spinor`.

1. **V_n and its norm.** `BinaryForm n` is the unchanged DS1 definition:
   mathlib's degree-n homogeneous `MvPolynomial (Fin 2) ℂ` submodule.
   Its coefficients, binomially weighted norm, and right complex-scalar
   quaternion correspondence are explained in [DS1](DS1.md).

2. **Polynomial action.** `substitution M j` is
   `C (M 0 j) * X 0 + C (M 1 j) * X 1`. `polynomialAction M` is mathlib's
   `aeval` at these two polynomials. Thus
   τ(M)p(X,Y)=p(aX+cY,bX+dY) for M=[[a,b],[c,d]].
   `polynomialRepresentation n` is a bundled mathlib `Representation` of the
   whole complex matrix monoid on V_n. Its identity, composition order,
   complex linearity and preservation of homogeneity are proved.
   `generalLinearPolynomialRepresentation` restricts it to mathlib's actual
   GL₂(ℂ). `polynomialAction_chainRule` gives the explicit polynomial gradient
   transformation in this convention.

3. **Quaternion embedding.** `quaternionMatrix q` is exactly
   [[t+ix,y+iz],[-y+iz,t-ix]]. `quaternionMatrixHom` bundles it as a real algebra
   homomorphism, and `quaternionMatrix_injective` proves injectivity.
   `quaternionMatrix_pack` proves that its action on the column (A,B) is left
   multiplication by q on `pack A B=A-jB`. `quaternionPolynomialRepresentation`
   and `unitQuaternionPolynomialRepresentation` are restrictions of the matrix
   action. The latter is a group representation; compact-group unitarity is
   not claimed in this delivery.

4. **Actual infinitesimal action.** `infinitesimal M p` is
   `(M00 X+M10 Y)p_X+(M01 X+M11 Y)p_Y`, using mathlib's polynomial partial
   derivatives. `infinitesimalAction m M` restricts it to V_(m+1).
   `polynomialRepresentation_hasDerivAt` proves that it is the analytic
   derivative at t=0 of τ(I+tM)p, in DS1's weighted norm. The complex and real
   parameter versions are both proved. `quaternionPolynomialRepresentation_hasDerivAt`
   proves the real derivative of τ(1+tv)p. The coefficient derivative is first
   proved for every polynomial by mathlib's derivative sum/product rules,
   then transported through the finite-dimensional coefficient equivalence.
   This ties the displayed operator to the representation, rather than leaving
   that correspondence as a premise. `infinitesimal_commutator` also proves
   [R_M,R_N]=R_(MN-NM).

5. **Generator signs and real scalars.** `infinitesimal_i`, `infinitesimal_j`,
   and `infinitesimal_k` give exactly
   i(X∂X−Y∂Y), −Y∂X+X∂Y, and i(Y∂X+X∂Y).
   `infinitesimal_real` proves dτ_n(r)=nr·Id, including the degree-zero case.

6. **T_n and C_v.** `polynomialFueterCoefficients p d` is the coefficient of
   X^d₀Y^d₁ in p_X-jp_Y, namely `pack ((pderiv 0 p).coeff d)
   ((pderiv 1 p).coeff d)`. It uses the **unnormalized** T_n; DS1's division
   by n does not enter SC2. `fueterCoefficients m` gives the same data in the
   finite degree-m row model. `connectionCoefficient q v` is the exact
   antisymmetric half-difference defining C_v. Its equality to
   conj(v)q−Re(conj(v)q) is proved directly. The sum uses the unchanged
   `MathResearch.Fueter.coordinateBasis`, mathlib's ordered basis (1,i,j,k).

7. **Exact conclusion.** `SC2_v1 (n : ℕ) (hn : 1 ≤ n) (q : ℍ)
   (p : BinaryForm n)` concludes both identities as equalities of functions
   from *all* exponent vectors `Fin 2 →₀ ℕ` to actual real quaternions.
   Thus the whole quaternion polynomial is identified, including coefficients
   outside the expected degree. Real multiplication by 2(n+1) or n+2 is
   expressed by mathlib's real scalar action. `SC2_v1_coefficients` supplies
   the equivalent finite row formulation, internally indexed by m=n−1.
   The factors at n=1 are 4 and 3.

## Proof and mathlib use

[PolynomialRepresentation.lean](../MathResearch/Spinor/PolynomialRepresentation.lean)
constructs the action, its chain rule, commutator identity and actual complex
and real derivatives. It uses `MvPolynomial.aeval`, homogeneous substitution,
`Representation`, `Matrix.GeneralLinearGroup`, scalar derivative sum/product
and composition rules, and finite-dimensional continuous linear equivalences.

[QuaternionMatrix.lean](../MathResearch/Spinor/QuaternionMatrix.lean) proves
that the matrix and column conventions match mathlib's real quaternions,
constructs the restricted representations, and records the generator and scalar
formulas. It reuses DS1's `pack` and the F1 coordinate basis.

[ProjectedConnection.lean](../MathResearch/Spinor/ProjectedConnection.lean)
first proves two identities for arbitrary binary polynomials. With E=X∂X+Y∂Y,
the full expression is 2ι(q)(E+2)grad p, and the connection expression is
ι(q)(E+3)grad p. These are exact differential-operator calculations, using
mathlib's product rule and commuting partials. Mathlib's homogeneous Euler
identity on grad p then gives E grad p=(n−1)grad p, producing the two constants
in SC2. Finally the proven matrix/quaternion correspondence translates the
polynomial columns into quaternion coefficients.

The main theorem has only the positive-degree and homogeneity hypotheses
visible above. It does not assume SC1, a flat connection, a unitary action,
Schmid covariance, or an imported Liu–Zhang theorem. SC1/SC3, the analytic
representation results and Hardy/cohomology constructions remain separate
formalization targets. This work makes no novelty claim about these identities.

## Reproduction and retained evidence

Lean 4.35.0 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` are unchanged.
From this standalone checkout:

```sh
python3 scripts/verify.py --clean-local
bash scripts/lake.sh env lean -DwarningAsError=true -DautoImplicit=false docs/SC2-statement-check.lean
```

The [statement-check source](SC2-statement-check.lean) prints the exact SC2
signature and verifies small convention comparisons: substitution order,
group inverse, derivative, quaternion generator signs, real scalar action,
unnormalized T_n, C_v, and the n=1 factors. The endpoint q=1, p=X has connection
contribution 3, confirming in a concrete case that the term is nonzero.

The [clean verification record](../evidence/SC2-v1-2026-10-31.json) retains source
and dependency fingerprints, the build outputs and the audit of every local
declaration, including private/generated helpers. The separate
[statement-check record](../evidence/SC2-statement-check-2026-10-31.json) retains
its exact output and fingerprints. Allowed axioms are only `propext`,
`Classical.choice`, `Quot.sound`; warnings are errors. Pinned upstream caches
are retained rather than independently rebuilt. These are Lean verification
and author correspondence records, not an independent review or a visitor
approval state.
