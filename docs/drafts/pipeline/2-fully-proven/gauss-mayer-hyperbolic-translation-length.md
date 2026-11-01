# Actual Mayer multipliers are hyperbolic translation lengths

- **Stage:** 2-fully-proven
- **Type:** Theorem (paper; Lean formalization required)
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md).
- **Inputs:** [primitive modular coding](../3-formalized/gauss-mayer-modular-primitive-coding.md), [actual multipliers](../3-formalized/gauss-mayer-primitive-orbit-words.md), [Euler product](../3-formalized/gauss-mayer-primitive-orbit-product.md).

## Statement

For each primitive pair cycle `c`, let `A_c` be its actual determinant-one
matrix, acting on the upper half-plane with the Poincaré metric. Then

```text
min_(z∈ℍ) dist(z,A_c z) = 2 log λ_c > 0.
```

Thus, defining `L_c` by the infimum of these actual displacements, the
certified determinant product has factors
`1−z^(2ℓ(c)) exp(−(w/2+m)L_c)`. At `z=1`, this fixes the length parameter
to `s=w/2`.

## Proof

Write `A=[[a,b],[c,d]]`, `λ=λ_c>1`, and `μ=λ⁻¹`. The existing source
theorems give `ad−bc=1`, `c>0`, and
`λ²−(a+d)λ+1=0`. Consequently `λ+μ=a+d`; both `λ` and `μ` solve this
characteristic quadratic, and `g=λ−μ>0`.

The real matrix

```text
C = [[(λ−d)/c, (μ−d)/g], [1, c/g]]
```

has determinant one. Its columns are rescaled eigenvectors, so
`AC=C diag(λ,μ)`. These assertions follow by clearing the nonzero
denominators `c,g`, using the characteristic quadratic and `ad−bc=1`.
In particular, `C` acts isometrically on the actual upper half-plane.

The diagonal matrix acts by `z↦λ²z`. The metric inequality
`dist(log Im z,log Im w)≤dist(z,w)` gives
`dist(z,λ²z)≥log(λ²)=2 log λ`. On the imaginary axis equality holds,
because equal real parts give equality in that metric inequality.
Conjugation by `C` transports the bound and its attaining point to `A`.
The displacement range therefore has least element `2 log λ`, so its
infimum is this number.

For the positive real base `λ`, complex exponentiation gives
`λ^(−w−2m)=exp((−w−2m)log λ)=exp(−(w/2+m)L_c)`.
Substitution into the already certified Euler product proves the stated
normalization on exactly its existing convergence domains.

## Scope

This identifies translation lengths of the actual matrices. Passing to
oriented/unoriented closed-geodesic classes and comparison with an independently
defined scattering determinant remain separate obligations.
