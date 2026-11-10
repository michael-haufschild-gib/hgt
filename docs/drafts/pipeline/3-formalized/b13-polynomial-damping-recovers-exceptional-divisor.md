# Divisor recovery at polynomial damping scales

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let a finite packet `F` contain every zero copy right of `θ<σ`, where
`½<σ<Re ρ<1` and `ξ(ρ)=0`. Put `d=1+#{q∈F:ρq≠ρ}`,
`a_A(t)=A log(t)/t`, and `φ(t)=−π/2+1/t`.
For every sufficiently large `A` and every eventually positive `h(t)→0`,
the literal rotated prime filter satisfies

`A_h^rot(t)/(h(t)^d Kφ(t^(−A),ρ−σ−it))`
`→ −mρ(ρ−1)Π_{q∈F,ρq≠ρ}(ρ−ρq) ≠ 0`.

The threshold on `A` is independent of spacing. For every `κ>0`, increasing
`A` if necessary makes the raw filter grow in norm when `h(t)=t^(−κ)`.
Unconditional dichotomies supply actual packets and top zeros whenever AAL
fails; no analytic input is assumed beyond the proved finite-layer profile.

## Proof

Choose a regular line `σ<c<Re ρ`. Uniform boundary-contour and reciprocal
mode bounds give

`normalized error ≤ CD t^(N+M) exp(−a_A(t)(Re ρ−c)t/2)`
`= CD t^(N+M−A(Re ρ−c)/2)`.

Thus `A≥2(N+M+1)/(Re ρ−c)` makes the error at most `CD/t`.
Every spacing factor cancels exactly. Positive Mellin real part excludes
Gamma poles, so the kernel is nonzero independently of mode growth. The
finite product of exponential differences gives the displayed divisor limit.

For polynomial spacing, the reciprocal contracted mode is at most
`D t^(M+dκ−A(Re ρ−σ)/2)`. Taking
`A≥2(M+dκ+1)/(Re ρ−σ)` makes this at most `D/t`.
Kernel nonvanishing then forces mode growth; the nonzero ratio limit transfers
that growth to the literal prime filter.

## Exact damping scale

Sample `j` has radius `t^(−A)exp(−2jh(t))`. Its complex damping parameter
`ε_j(t)` satisfies

`t^(A+1) Re ε_j(t) → 1`.

Indeed its scaled real part is
`exp(−2jh(t)) sin(1/t)/(1/t)`. Consequently, for every fixed sample `j`,
eventually for all real `x`,

`|exp(−ε_j(t)x²)|≤exp(−x²/(2t^(A+1)))`.

This gives Gaussian damping scale `t^((A+1)/2)`. It is a uniform kernel
envelope, not a truncation estimate for the complete weighted prime sum.

## Independent arithmetic comparison

With `w(T)=(log T)^(−2/3)(log log T)^(−5/3)/10^8`, the same observable obeys

`|A_h^rot(t)|≤C h^d t^N t^(A(1−σ)/2)`
`             · exp(−A log(t) w(t³+1)/4)`

for every fixed `A>0`, eventually uniformly in `0≤h≤1`.
Constants `C,N` are independent of `A`. The uniform-speed zero-free theorem
applies because `0<a_A(t)≤t/4` eventually.

## Lean declarations

`ExceptionalLayerTheory/PolynomialDampingReadsTheDivisor.lean` contains:

- `exists_polynomial_normalized_prime_error_bound`;
- `exists_polynomial_prime_filter_divisor_threshold`;
- `asymptoticAbscissaLaw_or_polynomial_divisor_readings`;
- `tendsto_polynomial_geometric_real_damping`;
- `eventually_polynomial_geometric_gaussian_envelope`;
- `exists_polynomial_prime_growth_threshold`;
- `asymptoticAbscissaLaw_or_polynomial_prime_growth`;
- `exists_polynomialPrimeDampingFilter_vinogradovKorobov_bound`.

The final direct source audit passes without warnings. All ten printed
transitive dependency lists contain only `propext`, `Classical.choice`,
and `Quot.sound`. The module is imported by the exceptional-layer umbrella.

## Remaining gap

Polynomial damping removes the exponential prime scale. It does not supply
prime cancellation: the upper bound still carries power `A(1−σ)/2`, while
the selected mode carries `A(Re ρ−σ)/2`, apart from fixed polynomial factors.
The positive gap `A(1−Re ρ)/2` remains. B13 is open.
