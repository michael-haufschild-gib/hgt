# The left continuation has square-integrable vertical traces

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** ECS Q4 and Q9.
- **Statement:** For every energy-domain profile and every `δ>0`, the meromorphic
  continuation has uniformly bounded vertical `L²` mass on `Re w≤-17/2-δ`.
  For `1/2<c≤4`, an explicit half-line `L²` profile `G_c` represents
  `stateMeromorphic W₀ F (-(z+c)-8)=laplaceRay G_c z` on `Re z>0`.
  Consequently its norm is at most `‖G_c‖₂/sqrt(2(-Re w-c-8))` when `Re w<-c-8`.

## Proof

Write `ω` for the archimedean Lévy density and `L` for the negative-half-line
Laplace transform. The existing near/far bounds give `ω(r)≤4/r`. Carleman's
inequality therefore puts `K_F(v)=∫(t>0)ω(v+t)F(-t)dt` in `L²`, with squared
mass at most `16π²‖F‖₂²`. Expanding `ω` into its geometric modes and integrating
the absolutely summable resolvents proves `JF(-z)=laplaceRay K_F z` for `Re z>0`.

For `c≤4`, confinement puts `D_c(u)=exp(-cu)F(u)` in `L²`. Translation and
restriction bound the norm of
`P_(c,n)(v)=Λ(n)n^(-1/2-c)D_c(v-log n)` by
`Λ(n)n^(-1/2-c)‖D_c‖₂`. For `c>1/2` these coefficients are summable. Thus
`P_c=Σ_n P_(c,n)` exists in the half-line Hilbert space. Continuous Laplace
evaluation commutes with this sum. Translating each integral gives exactly
`laplaceRay P_c z=primeHead F (-(z+c))`.

The full datum is

`G_c=(-1/a)[exp(-cv)K_F(v)+P_c(v)-LF(1/2)exp(-(c+1/2)v)-LF(-1/2)exp(-(c-1/2)v)]`.

All four terms lie in `L²`. Their Laplace transforms reproduce the two heads and
the two charges in the exact left-continuation formula. Half-line Plancherel
bounds every vertical square integral by `‖G_c‖₂²`; Cauchy–Schwarz gives the
pointwise inverse-square-root bound. For arbitrary `δ>0`, choosing
`c=1/2+min(δ/2,1/2)` puts every requested vertical line strictly inside this
Hardy half-plane.

## Lean

All three modules passed final plain Lean checks and are umbrella-wired.

- `TheLevyHeadIsAHardyTransform`: `memLp_levyHeadProfile`,
  `levyHeadTerm_neg_eq_laplaceRay`, `isHalfPlaneHardy_levyHeadTerm`.
- `ThePrimeHeadsAreHardyTransforms`: `summable_primeHeadDatumLp`,
  `laplaceRay_primeHeadProfile`, `isHalfPlaneHardy_primeHead`.

- `TheLeftContinuationHasSquareIntegrableVerticalTraces`:
  `stateMeromorphic_eq_laplaceRay_left`, `norm_stateMeromorphic_left_le`,
  `isHalfPlaneHardy_leftContinuation`,
  `exists_bound_vertical_stateMeromorphic_left`.

## Boundary of the result

The convergent half of Q4 needs control toward the pole strip and remains open.
Before damping, the negative charge subtracts `LF(-1/2)exp(v/2)` from the prime
profile. Separate absolute bounds on prime heads and charges require `c>1/2`;
advancing this boundary requires control of their arithmetic cancellation.
No boundary value of `F` or leading asymptotic coefficient is asserted.
