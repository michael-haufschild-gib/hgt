# Complete conductor residuals retain their horizon decay

- **ID:** complete-conductor-horizon-decay
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For each positive conductor `m`, the literal complete Weil residual satisfies `||W_(N,c)v_m-E_m(c)v_m||²≤K_m(c^5/log N+c^10(log N/N)^2)` uniformly for `c≥1`, `N≥4(exp(1)+3)^2c²`, beyond a fixed horizon.

## Paper proof

Use the exact eight-term complete residual identity. The prime-only residual has normalized square budget `O_m(1/log N)`. The self replacement is `O_m(c²/N²)`. The center, separated archimedean cross, and pole replacement budgets are respectively `O_m(c²/log N)`, `O_m(c^4/log N)`, and `O_m(c^4/log N)`. The full signed near-Gamma/downward source and near-center correction are each `O_m(c^5/log N)`.

The actual upward source has the Lean-proved two-rate estimate in [upward-prime-errors-retain-their-horizon-decay.md](../3-formalized/upward-prime-errors-retain-their-horizon-decay.md). Its exact conductor normalization contributes only the fixed factor `1/φ(m)`.

For `c≥1` and `log N≥1`, every `c^k/log N` with `k≤5` is at most `c^5/log N`, and `c²/N²≤c^10(log N/N)^2`. The square of the signed eight-term sum is bounded by eight times the sum of squares. All actual prime powers, orientations, poles, and boundary terms remain present.

## Scope

This is a stronger actual-source bound, not a growing-conductor theorem. The constants still depend on the conductor, and effective capture of negative eigenvectors remains open. No quasi-RH conclusion or impossibility result follows yet.

## Lean proof

`CriticalArithmeticCorrelationTheory/CompleteConductorResidualsRetainTheirHorizonDecay.lean`:

- `exists_completeWeil_completedConductor_residual_horizon_bound`
- `exists_tiltedUnitSpline_completedConductor_residual_horizon_bound`

Both pass `lake --old env lean`; transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
