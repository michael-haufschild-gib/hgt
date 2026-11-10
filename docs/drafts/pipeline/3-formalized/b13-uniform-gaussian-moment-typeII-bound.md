# Uniform Gaussian moment type-II bound

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let `c=(typeIILong U)*(typeIIShort V)` be the actual arithmetic
convolution, `ε=α−iξ`, and

`T₁=(ε/t) Σ_{n≥0} c(n) GaussianWeight(σ−2,α,ξ,t,n)`.

For `0≤σ<1`, `ξ>0`, `t≥1`, `ξ/(2t)≤α≤ξ`, and
`πU≥128t log t`, `V≥2t`, the series converges absolutely.
For every physical scale `X≥1` with `αX²≥2`,

`|T₁|≤16 sqrt(C/t) [1/(2^(1−σ)−1)+12]`
`       × X^(1−σ) [2+log X/log 2]^4`,

with an absolute `C>0`, independent of every parameter. One may always
choose `X=max(1,sqrt(2/α))`. Finite intervals obey a corresponding
bound uniform in both endpoints. No zero-location premise enters.

## Dyadic proof

Put `q=2^(1−σ)`, so `1<q≤2`. The all-scale theorem retains
`Eσ,α(D,M)=Wσ²(1+log(2D))(1+log(2M))⁴ exp(−αD²M²)`.
Its square root at `D=2^j`, `M=2^k` satisfies

`sqrt(E)≤8q^(j+k)(j+k+1)^3 exp(−α4^(j+k)/2)`.

Indeed `Wσ=q^(j+k)`, `1+log(2·2^j)≤2(j+1)`, and the square root
of the long-factor logarithm is at most that logarithm. There are at
most `n+1` rectangles with `j+k=n`. Thus the rectangular sum is at
most eight times

`Σ_n q^n(n+1)^4 exp(−α4^n/2)`.

Choose `R` with `α4^R≥2`. For `n<R`, discard the exponential and
sum the geometric progression, costing
`q^R(R+1)^4/(q−1)`. For `n=R+l`, use
`R+l+1≤(R+1)(l+1)`, `l+1≤2^l`, and
`exp(−4^l)≤6/64^l`, from the cubic term of the exponential series.
The tail is at most
`6q^R(R+1)^4 Σ_l2^(−l)≤12q^R(R+1)^4`.

The actual finite convolution therefore has bound

`8 sqrt(C/t) [1/(q−1)+12] q^R(R+1)^4`,

independent of the endpoints. For any `X≥1`, select
`2^k≤X<2^(k+1)` and `R=k+1`. Then `α4^R≥2`,
`q^R≤2X^(1−σ)`, and `R+1≤2+log X/log 2`, proving the stated bound.

## Infinite arithmetic sum

The exact Vaughan coefficients satisfy
`|typeIILong U(d)|≤Λ(d)≤d` and
`|typeIIShort V(m)|≤1+τ(m)≤2m` for positive factors.
Every divisor-antidiagonal term is at most `2n`, and `τ(n)≤n`, so
`|c(n)|≤2n²`. For `σ≥0`, the shifted Gaussian summand has norm at
most `2n⁴ exp(−αn²)` for `n≥1`; its value at zero vanishes.
Polynomial-Gaussian summability proves absolute convergence. The
endpoint-uniform bound passes to the infinite sum by continuity of norm.

## Scope

This closes type-II truncation and infinite tails while retaining the
square-root-of-height saving and the exponent `X^(1−σ)`. Type-I moments
and the complete raw prime sum are handled in
`b13-complete-infinite-gaussian-moment-bound.md`. Arithmetic control
retaining pole/filter cancellation remains before comparison with the
selected divisor signal. B13 is not proved.

## Lean declarations and audit

All declarations are in `GaloisForLFunctions.ExceptionalLayerTheory`,
module `GaussianMomentInfiniteTypeII.lean`:

- `sum_dyadic_gaussian_fourth_le`
- `exists_gaussianMoment_physical_scale`
- `norm_gaussianPrimeWeight_exact`
- `sum_sqrt_gaussianMomentRectangleEnergy_le`
- `exists_gaussianVaughan_moment_uniform_typeII_bound`
- `summable_gaussianVaughan_moment_typeII`
- `exists_gaussianVaughan_moment_infinite_typeII_bound`
- `exists_gaussianVaughan_moment_physical_typeII_bound`
- `gaussianMoment_physicalScale_admissible`

The final direct source check with `lake --old env lean` passes without
warnings. All nine printed transitive axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`. The module is imported by
`ExceptionalLayerTheory.lean`; no umbrella build was run.
