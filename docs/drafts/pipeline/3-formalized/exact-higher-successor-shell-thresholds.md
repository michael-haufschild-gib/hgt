# Exact higher successor-shell thresholds

- **Stage:** 3-formalized
- **Statement:** For `N,k≥1`, a pair `1≤a≤N`, `b≥a+k` lies within logarithmic
  width `c/N` exactly when `N(log(N+k)-log N)≤c`.
- **Bounds:** `k-k²/N ≤ N(log(N+k)-log N) < k`; the threshold tends to `k`.
- **Consequence:** Every fixed `c<k` eventually excludes all gaps of size at least `k`.
- **Scope:** Geometric eligibility; nonzero prime coefficients and profile correlations remain
  separate requirements.

The smallest logarithmic gap occurs at `(N,N+k)`, since
`(X+r)/X ≤ b/a` for `0<a≤X` and `a+r≤b`. The upper logarithm bound gives the
strict upper threshold; `log(1+k/N)≥k/(N+k)` gives the lower bound and limit.

Lean: `CriticalArithmeticCorrelationTheory/ExactHigherShellThresholds.lean`.
Main declarations: `exists_successor_gap_iff`, `exteriorShellOverlap_ge`,
`exteriorShellOverlap_lt`, `tendsto_exteriorShellOverlap`, `eventually_no_successor_gap`.
Direct `lake --old env lean` check passed; printed dependencies contain only
`propext`, `Classical.choice`, and `Quot.sound`. Programme umbrella imports the module.
