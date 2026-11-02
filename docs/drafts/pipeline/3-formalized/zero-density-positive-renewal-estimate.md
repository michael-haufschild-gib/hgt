# Positive renewal and regular variation at zero density

- **ID:** zero-density-positive-renewal-estimate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Γ12; positive renewal at zero logarithmic prime density.
- **Statement:** Put `g=1*ω_P`, `G_N=Σ_(n≤N)g(n)/n`, and `M_N=Σ_(n≤N)(g(n)/n)log(N/n)`. If `A_P(N)/(1+log N)→0`, then for every `ε>0` some `C` satisfies `|G_N log N−3M_N|≤εM_N+C G_N` at every horizon.

## Proof

The positive kernel `K=(1+ω_P)Λ` has cumulative harmonic mass
`B_N=2log N−2A_P(N)+O(1)`. The non-prime prime-power terms are
bounded, and Mertens' theorem controls the full-prime terms. Hence
`|B_N−2log N|≤εlog N+C_ε` for every horizon after absorbing the
finite initial segment.

Swap the finite sums in the exact renewal identity:
`Σ_(n≤N)g(n)log n/n=Σ_(m≤N)(g(m)/m)B_⌊N/m⌋`.
Nonnegative weights bound the error by
`εΣ(g(m)/m)log⌊N/m⌋+C_εG_N`. The latter logarithmic moment lies
between `M_N−(log 2)G_N` and `M_N`. The asserted inequality follows.

## Real logarithmic horizons

For `G(u)=G_⌊e^u⌋` and
`J(u)=Σ_(n≤e^u)(g(n)/n)(u−log n)`, the moment `J` is continuous,
has right derivative `G` everywhere, and satisfies `J(u)≥u` for
`u≥0`. Each new summand enters with value zero.

Since `0≤u−log⌊e^u⌋≤log 2`, the integer estimate gives
`|uG(u)−3J(u)|≤εJ(u)+(C+2log 2)G(u)` for every `u≥0`.

## Regular variation and uniform growth

The relative estimate first gives `2J≤uG≤4J` eventually, then
`uG/J→3`. Right-derivative comparison for `log J` gives, uniformly
for large `a≤b`,
`(3−ε)log(b/a)≤log(J(b)/J(a))≤(3+ε)log(b/a)`.
Hence `J(cu)/J(u)→c³` and `G(cu)/G(u)→c²` for every `c>0`.

The same bounds give `G(u)/u^α→∞` for every `α<2` and
`G(v)/v≤2G(u)/u` uniformly for sufficiently large `v≤u`.
The latter uses the lower exponent two for `J`, together with
`2J≤uG≤4J`; it controls all earlier large horizons at once.

For every `ε>0`, uniformly for `c≥1` and sufficiently large `u`,
`½c^(2−ε)G(u)≤G(cu)≤2c^(2+ε)G(u)`.
In particular the Dirichlet series converges and
`Σ_(n≥1)(g(n)/n)exp(−log n/u)≤C G(u)`.
To prove this, cover each damped term by its block `k=⌊log n/u⌋`.
The full positive sum is bounded by
`2G(u)Σ_(k≥0)e^(−k)(k+1)³`; this polynomial-geometric series converges.
Uniformly bounded nonnegative finite sums establish summability as well as the bound.

## Lean

`RenormalizedIntersectionTheory/ThePositiveDivisorMeanSatisfiesTheRenewalEquation.lean`:

- `logMoment_signDivisorCount_eq`
- `abs_positive_divisor_renewal_equation_le`
- `exists_abs_positive_divisor_renewal_equation_le`

`RenormalizedIntersectionTheory/ThePositiveDivisorMeanAtRealLogarithmicHorizons.lean`:

- `continuous_realPolarMoment`
- `hasDerivWithinAt_realPolarMoment`
- `le_realPolarMoment_signDivisorCount`
- `exists_abs_real_positive_divisor_renewal_equation_le`

`RenormalizedIntersectionTheory/ThePositiveDivisorMeanVariesRegularly.lean`:

- `tendsto_positive_divisor_logarithmic_derivative`
- `exists_positive_divisor_log_scaling_bounds`
- `tendsto_positive_divisor_polarMoment_ratio`
- `tendsto_positive_divisor_harmonicMean_ratio`
- `exists_positive_divisor_harmonicMean_uniform_comparison`
- `tendsto_positive_divisor_harmonicMean_div_rpow_atTop`

`RenormalizedIntersectionTheory/ThePositiveDivisorMeanControlsItsLaplaceTransform.lean`:

- `exists_positiveDivisorMean_uniform_power_comparison`
- `exists_positiveDivisorMean_laplace_comparison`

Kernel checks passed. All audited capstones use only
`propext`, `Classical.choice`, and `Quot.sound`.
