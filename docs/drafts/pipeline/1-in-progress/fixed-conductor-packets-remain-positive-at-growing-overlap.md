# Fixed conductor packets at growing overlap

- **ID:** fixed-conductor-packets-remain-positive-at-growing-overlap
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** CACT growing-overlap source problem; RHTower quantitative prime errors;
  completed-shell Fourier positivity.

## Target

For the explicit tilted unit spline, every fixed finite set of positive
conductors and every fixed `A>0`, seek one horizon beyond which the actual
complete Weil form is positive on their entire Ramanujan span,
simultaneously for `1≤c≤(log log N)^A`. Retain a lower bound proportional
to `(1+c)⁻⁷` times squared conductor coefficients.

This would control actual signed source packets at prescribed unbounded
overlap. The conductor set stays fixed; full-matrix positivity and RH
remain separate questions.

## Proposed mechanism

1. Use `RHTower.exists_primeProgressionTheta_power_log`, retaining proper
   prime powers and non-unit classes, to bound each actual residue source
   by its mean with every inverse-logarithmic error rate.
2. Abel summation transfers cumulative rates to residue Mertens finite
   parts and then to reciprocal shell weights. Flatness below `1/(2c)`
   gives a polynomial-in-`c` error when `X/c` is large. For the global
   bound, support forces active `k≥X/c`; `ψ(X)≤CX` then bounds the full
   shell correction by `O(c²)`. Split the harmonic row sum at
   `X=2c exp(sqrt(log N))`; its remaining harmonic mass is
   `O((log c+sqrt(log N))/log N)`.
3. Use `N≥c` before bounding geometry: exterior and near-row offsets are
   `O(c)`, avoiding bounds exponential in `c`. Prove a polynomial-in-`c`
   squared bound for every remaining literal residual.
4. `TheTiltedSplineHasAPolynomialConductorFloor` proves
   `∫_(t>c)|φ̂(2πt)|²dt ≥ C/c⁷` for `c≥1`, with explicit `C>0`.
5. Combine these actual residual bounds, finite-family Gram control, and
   the completed conductor tail floor. Every power of `log log N` is
   dominated by the resulting power of `log N`.

## Open dependencies

The polynomial conductor floor and cumulative residue-source rates passed
Lean audits. Quantitative Mertens transfer, the logarithmic harmonic
cutoff bound and the global polynomial shell bound are also formalized.
Weighted shell rates are formalized. Polynomial geometry is under formalization;
`SignedArithmeticHodgeTheory.exists_uniform_primeMertensSquareBudget` supplies
the stronger horizon-independent prime-ratio residual bound. Complete
quasimodes and final packet positivity remain open. Supporting lemmas
receive no separate contribution count. Corpus search found fixed-overlap
quasimodes and actual quantitative progression prime sums; it did not find
this growing-overlap signed-packet estimate.
