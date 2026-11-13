# Single-point inner factor is a pure delay

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** A bounded analytic disk function, continuous and nonzero on the closed disk except possibly at `1`, has canonical inner factor `c exp(-d(1+z)/(1-z))`, where `|c|=1` and `d≥0`.
- **Role:** Supporting classification for critical-state outerness; not separately counted.

## Proof

Write the canonical bounded factorization `f=IO`. Since `f` has no interior zeros, `u=-log|I|` is harmonic and nonnegative. The outer bound gives `u≤log(bd(O))-log|f|`. On every closed angular interval avoiding `1`, continuity and nonvanishing give a positive minimum for `|f|` on a slightly wider compact radial sector. Thus `u` is uniformly bounded there.

The inner factor has unimodular boundary values. Its verified almost-everywhere radial subsequence therefore makes `u` tend to zero. Circle-null sets pull back to null sets in one angular period, then on the whole real line by countably many period translations.

Represent `u` by a finite positive angular Poisson measure `ν`. The verified local mass lemma and dominated convergence give zero mass to each closed interval avoiding `1`. Rational intervals cover that open complement. Hence `ν` is concentrated on angles representing `1`, and `u(z)=d P(z,1)`, with `d=ν(ℝ)≥0`.

Since `P(z,1)=Re((1+z)/(1-z))`, the analytic function `I(z) exp(d(1+z)/(1-z))` has constant modulus one. The maximum-modulus principle makes it a unimodular constant. This proves the stated classification.

## Formalization

`exists_innerFactor_eq_unit_mul_delay` in `HTGeometry/HardyBoundary/DiskMultiplierInnerDelay.lean` proves the exact classification. It uses the verified defect and singular-support modules. Final plain Lean audit passed; transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. All three modules are wired. Actual critical-state delay removal and causal cyclicity remain separate steps.
