# One critical Steklov schedule is complete

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Original obstacle A3: one explicit constant `K>0` such that eventual
  complete Weil positivity for `steklovDCProfile` at overlap
  `K (log log N)(log log log N)^2` is equivalent to RH.

## Established boundary

`ABoundedOverlapRateSeesASemilocalWindow.steklovDCProfile_window` covers tests
supported in `[-R,R]` when `288 e blockSize(R+1)<K`.
`TheSteklovScheduleReachesTheIndex.steklovDCProfile_atomicGram_reaches_index`
exhausts the full Weil index when the last logarithm has exponent `β>2`.
Neither supplies a constant independent of the negative witness's support.

## Open input

Remove the support dependence in the critical-scale synthesis or construct
another complete detector at one fixed critical multiple. Common translation
preserves Weil Gram matrices, but does not reduce support diameter or the ratio
between the largest and smallest arithmetic nodes.

For the existing quadrature, `p=2 ceil(log log κ)+2` and
`r=p log²(p+3)(b+Bφ κ+p)/n`, with horizon `N=n B`. At critical overlap,
the profile term retains the factor `Bφ B/K`. The proved bound
`r≤24b log³N/n+144log⁴N/n+24Bφ B/rate` therefore cannot certify every
support block at a single rate. This is a limitation of that bound, not a
disproof of single-`K` completeness.

The equivalence quantified over all `K` yields an existential detecting `K`
by a classical split on RH. That logical consequence supplies no explicit
schedule and is not counted as the requested solution.

## Lean status

No new theorem claimed.
