# Uniform rough means without a density error rate

- **ID:** zero-density-uniform-rough-means
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Γ12, zero-Euler-mass endpoint.
- **Statement:** Let `ω=ω_P`, `A_P(N)=Σ_(p∈P,p≤N)log p/p=o(log N)`, `S(N)=Σ_(n≤N)ω(n)/n`, and `δ_Q=Π_(p∈P,p<Q)(p−1)/(p+1)`. There are positive constants `A,B` such that, for all sufficiently large `N`, uniformly for `3≤Q≤N`,
  `|Σ_(n≤N, n Q-rough)ω(n)/n|≤A S(N)/(log Q·δ_Q)+B`.

## Proof

For any real completely multiplicative contraction `f`, the divisor convolution
`g=1*f` is nonnegative: every prime-power coefficient is a nonnegative geometric
sum. The divisor-count rounding estimate gives `Σ_(n≤N)f(n)/n≥−1`.
The full von Mangoldt identity, the inequality `f(d)S(Y)≤S(Y)+2`, and Mertens'
first bound then give
`S(N)log N≤2G(N)+(16+3log 4)(1+log N)`.
Thus the rough flip satisfies `|S_Q(N)|≤2G_Q(N)/log N+O(1)` universally.

For the original prime flip, positive renewal proves regular variation of
`G(e^u)` with index two and signed recovery `uS(e^u)/G(e^u)→2`.
Its uniform power bound `G(e^((k+1)u))≤C(k+1)³G(e^u)` and positive block summation
give the convergent Laplace estimate `F_g(1+1/u)≤C'G(e^u)`.

Absolute convergence and the completely multiplicative Euler product give the
exact identity
`F_(1*ω_Q)(1+1/u)=F_g(1+1/u)Π_(p<Q)(1−ω(p)p^(−1−1/u))`.
For `x=1/p`, `t=log p/u`, `D=1−ω(p)x≥1/2`,
`1−ω(p)xe^(−t)≤D+xt≤De^(2xt)`.
When `log Q≤u` and `u≥1`, Mertens' first estimate bounds the product of these
tilts by a universal constant. The untilted head is the ordinary Mertens
product divided by `δ_Q`, hence is `O(1/(log Q·δ_Q))`.

Positivity gives `G_Q(e^u)≤e F_(1*ω_Q)(1+1/u)`. Combining the preceding bounds
with signed recovery yields the stated uniform rough estimate. No exact Euler
asymptotic for `S(N)` and no positive limiting Euler mass are required.

## Lean

Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory`.

- `TheRoughFlipHasAPositiveDivisorMean.lean`: `harmonicSum_mul_log_le_two_divisorMean`, `abs_roughFlipHarmonicSum_le_divisorMean`.
- `ThePositiveDivisorMeanControlsItsLaplaceTransform.lean`: `exists_positiveDivisorMean_laplace_comparison`.
- `TheDivisorDirichletSeriesRetainsPrimeRemoval.lean`: `hasSum_realDivisorDirichletTerm`, `realDirichletSeries_roughGauge_eq`, `realDivisorDirichletSeries_roughGauge_eq`.
- `TheFiniteEulerHeadControlsPrimeRemoval.lean`: `exists_uniform_tiltedPrimeRemovalFactor_le`.
- `TheZeroDensityRoughMeanIsUniform.lean`: `exists_eventually_uniform_zeroDensity_roughMean_bound`.

All modules passed their direct Lean checks. Audited capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
