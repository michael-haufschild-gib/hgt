# Finite-radius torsion self-energy

- **ID:** hhac-finite-radius-torsion
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0711 §2.11, B88
- **Statement:** After removing diagonal self-energy and the universal radial
  term, a finite torsion cloud has a quadratic, explicitly bounded radial error.

## Exact target

For distinct unit complex numbers `z_i`, real charges `a_i`, and `0<r<1`,
put `d_ij=|z_i−z_j|²`, `u=(1−r)²/r`. The identity

`|1−r z_i conjugate(z_j)|² = r d_ij+(1−r)²`

implies that the off-diagonal kernel, after adding `log r/2`, differs from
`−log|z_i−z_j|` by `−log(1+u/d_ij)/2`. Its magnitude is at most
`u/(2d_ij)`. Summing against signed charges gives an explicit inverse-chord
cost; the universal radial term is determined by total charge and square mass.

## Mechanism and scope

Use the unit-circle norm identity and `0≤log(1+t)≤t` for `t≥0`.
The existing Abel-energy theorem proves positivity and a limiting
renormalization but supplies no finite-radius error modulus. This target
retains the exact divergent diagonal and quantifies the remaining error.

It does not prove payment of self-energy by the archimedean reserve, and
does not construct a global arithmetic height. Those remain open.

## Dependencies

`ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy`
defines the actual torsion energies and their limiting prime kernel.
Check for existing quantitative radial estimates before claiming a new tool.

## Paper proof

For `|w|=1`, expansion of the squared norm gives
`|1−rw|²=r|1−w|²+(1−r)²`. If `r>0` and `w≠1`, both the squared chord
and `1+(1−r)²/(r|1−w|²)` are positive. Taking the real logarithm and
dividing by two gives the stated kernel identity. For `t≥0`,
`0≤log(1+t)≤t`; this proves the signed kernel correction and its upper bound.

Let `O_m` denote the primitive roots of order `m`, and remove coincident
pairs from `O_m×O_n`. Write `c(m,n)` for their number and
`C(m,n)=Σ_{z≠w}|z−w|⁻²`. Both are literal finite sums. Then

`T°_r(m,n)+c(m,n)log(r)/2 = −I(m,n)−R_r(m,n)`,

where `0≤R_r(m,n)≤(1−r)² C(m,n)/(2r)`.
The boundary sum is exactly `I(m,n)` because the existing definition's
coincident terms are zero. This use of the total real logarithm is only
at the boundary; the finite-radius diagonal is retained explicitly.

On a single orbit the removed diagonal has `φ(n)` terms, each
`−log|1−r|`. Hence

`T_r(n,n)+φ(n)log|1−r|+c(n,n)log(r)/2 = −I(n,n)−R_r(n,n)`.

For signed coefficients, the triangle inequality bounds the total error
by `(1−r)²/(2r)` times the sum of absolute coefficients weighted by
`C(m,n)`. No sign of a renormalized quadratic form is inferred.

## Relation to existing regulators

`ArithmeticIntersectionTheory.TheSpacingRegulatorRemovesTheAnomaly`
already constructs positive spacing-dependent regulators and identifies
their indefinite limits. The additional target here is a finite-radius
error formula, not another limiting positivity claim. Uniform conductor
estimates for `C(m,n)` and payment of the diagonal remain open.
