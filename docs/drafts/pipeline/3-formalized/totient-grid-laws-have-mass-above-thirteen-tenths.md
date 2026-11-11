# Totient grid laws exceed the positivity threshold

- **Stage:** 3-formalized
- **Parent:** [Periodic pair-law interpolation](totient-grids-obstruct-seventy-percent-at-every-bandwidth.md).

For every sufficiently large integer `L`, assign weights `φ(m)/L²` to the
uniform cyclic grids of orders `1≤m≤L`, and the remaining weight to order
`L+1`. These are nonnegative probability weights. Their Fourier coefficients
are nonnegative; the divisor identity `Σ_{d|k}φ(d)=k` gives exactly `k/L²`
for `1≤k≤L`.

After normalizing the period mass to `L`, the common origin has mass

```
A_L = (1/L) Σ_{m≤L} φ(m)/m
      + L/(L+1) (1 − (1/L²) Σ_{m≤L} φ(m)).
```

Möbius inversion and the absolutely convergent Möbius square series give
`(1/L)Σφ(m)/m → 6/π²`. Linear weighted averaging then gives
`(1/L²)Σφ(m) → 3/π²`. Hence `A_L → 1+3/π² > 13/10`, using `π²<10`.

Lean: `TransThresholdPairCorrelation/TotientGridPairLaw.lean`.
Main declarations: `totientGridCoefficient_eq_ramp`,
`totientGridCoefficient_nonneg`, `tendsto_totientGridOriginMass`,
`exists_totientGridOriginMass_gt`. Module checked and imported by its umbrella.

This proves the finite arithmetic law. Its continuous Fourier interpolation
and positivity-preserving regularization remain separate obligations.
