# Compact-profile tails dominate every exponential

- **Stage:** 3-formalized
- **Wall:** Σ1d.
- **Statement:** Every nonzero real compact `C²` profile on `[0,1]` satisfies, for every `ε>0`,
  `∫_(t>c)|φ̂(2πt)|² dt ≥ exp(-εc)` eventually in `c`.
  A positive prefactor makes the bound valid for every `c≥0`.
  Consequently `E_m(c)≥aε exp(-εc/m)` for every `c>0`, `m>0`.

## Proof

The compact Fourier transform has an integrable quadratic weighted
logarithm, by the corpus Paley–Wiener Poisson majorant. A nonzero real
spectral value and continuity supply its required upper-half-plane
witness. The entire transform's zeros are countable; their real preimage
is null. Frequency rescaling therefore gives the weighted-log integral
for the actual shell spectrum `H`.

If `∫_(u>c)H(u)<η=exp(-εc)`, then almost everywhere
`εc+1≤H(u)/η+|log H(u)|`. On `(c,2c]`, the quadratic logarithmic
weight's denominator is at most `Dc²`, with fixed `D>0`.
Integrating gives
`c(εc+1)<1+Dc²∫_(u>c)|weighted log H(u)|`.
The last integral tends to zero, contradicting the inequality for large
`c`. The existing exponential floor absorbs bounded `c`. The first
coprime spectral repayment transfers the tail floor to conductor energy.

## Lean

`CriticalArithmeticCorrelationTheory/IntegrableLogarithmsForceSubexponentialTails.lean`:
`eventually_exp_le_tail_of_integrable_log_weight`.

`CriticalArithmeticCorrelationTheory/EveryCompactProfileHasSubexponentialConductorFloors.lean`:
`eventually_exp_le_shell_tail`, `exists_subexponential_shell_tail`,
`exists_subexponential_completedConductor_floor`.

Direct checks passed. All four transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Both umbrella imports are wired.
The arbitrary-multiple log-log coercivity assembly remains separate.
