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
2. Apply Abel summation directly to this cumulative source with weight
   `W(u)/u`. Flatness below `1/(2c)` gives a polynomial-in-`c` weighted
   error when `X/c` is large. A separate Mertens window bound gives a
   polynomial global error. Split the harmonic row sum at
   `X=2c exp(sqrt(log N))`; the remaining harmonic mass is
   `O((log c+sqrt(log N))/log N)`.
3. Use `N≥c` before bounding geometry: exterior and near-row offsets are
   `O(c)`, avoiding bounds exponential in `c`. Prove a polynomial-in-`c`
   squared bound for every remaining literal residual.
4. The tilted spline Fourier formula should give
   `∫_(t>c)|φ̂(2πt)|²dt ≥ C(1+c)⁻⁷`, with `C>0`.
5. Combine these actual residual bounds, finite-family Gram control, and
   the completed conductor tail floor. Every power of `log log N` is
   dominated by the resulting power of `log N`.

## Open dependencies

The quantitative residue transfer, polynomial geometry, and explicit tail
floor require complete paper proofs and Lean audits. No theorem or
contribution is counted. Corpus search found fixed-overlap quasimodes and
actual quantitative progression prime sums; it did not find this
growing-overlap signed-packet estimate.
