# Actual Mayer multipliers are hyperbolic translation lengths

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md).
- **Inputs:** [primitive modular coding](gauss-mayer-modular-primitive-coding.md), [actual multipliers](gauss-mayer-primitive-orbit-words.md), [Euler product](gauss-mayer-primitive-orbit-product.md).

## Statement

For each primitive pair cycle `c`, let `A_c` be its actual determinant-one
matrix, acting on the upper half-plane with the Poincaré metric. Then

```text
min_(z∈ℍ) dist(z,A_c z) = 2 log λ_c > 0.
```

The same minimum formula holds for every nonempty pair word and its actual
expanding multiplier.

Thus, defining `L_c` by the infimum of these actual displacements, the
certified determinant product has factors
`1−z^(2ℓ(c)) exp(−(w/2+m)L_c)`. At `z=1`, this fixes the length parameter
to `s=w/2`.

## Proof

Write `A=[[a,b],[c₀,d]]`, `λ=λ_c>1`, and `μ=λ⁻¹`. The existing source
theorems give `ad−bc₀=1`, `c₀>0`, and
`λ²−(a+d)λ+1=0`. Consequently `λ+μ=a+d`; both `λ` and `μ` solve this
characteristic quadratic, and `g=λ−μ>0`.

The real matrix

```text
C = [[(λ−d)/c₀, (μ−d)/g], [1, c₀/g]]
```

has determinant one. Its columns are rescaled eigenvectors, so
`AC=C diag(λ,μ)`. These assertions follow by clearing the nonzero
denominators `c₀,g`, using the characteristic quadratic and `ad−bc₀=1`.
In particular, `C` acts isometrically on the actual upper half-plane.

The diagonal matrix acts by `z↦λ²z`. The metric inequality
`dist(log Im z,log Im w)≤dist(z,w)` gives
`dist(z,λ²z)≥log(λ²)=2 log λ`. At `z=i` equality holds,
because the two points have equal real parts.
Conjugation by `C` transports the bound and its attaining point to `A`.
The displacement range therefore has least element `2 log λ`, so its
infimum is this number.

For the positive real base `λ`, complex exponentiation gives
`λ^(−w−2m)=exp((−w−2m)log λ)=exp(−(w/2+m)L_c)`.
Substitution into the already certified Euler product proves the stated
normalization on exactly its existing convergence domains.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerHyperbolicLength.lean`, namespace
`GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolicLength`:

- `pairElement_minimum_displacement`: attained sharp bound for every nonempty pair word.
- `orbitElement_minimum_displacement`: the primitive-cycle specialization.
- `orbitTranslationLength_eq`: actual displacement infimum equals `2 log λ_c`.
- `orbitTranslationLength_pos`: strict positivity.

`RenormalizedIntersectionTheory/GaussMayerPrimitiveOrbitProduct.lean`, namespace
`GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitProduct`:

- `orbitWeight_eq_translationLength`: exact geometric normalization of each source factor.
- `exists_signed_determinant_translationLength_eulerProduct`: local product for `Re w>1`.
- `signed_determinant_translationLength_eulerProduct_on_closed_unit`: product on `|z|≤1` for `Re w>2`.
- `signed_determinant_one_eq_translationLength_eulerProduct`: specialization at `z=1`.

Both direct production checks passed without diagnostics. All eleven theorem
audits across both modules contain only `propext`, `Classical.choice`, and
`Quot.sound`. The programme umbrella imports both modules.

## Scope

This identifies translation lengths of the actual matrices. Passing to
oriented/unoriented closed-geodesic classes and comparison with an independently
defined scattering determinant remain separate obligations.
