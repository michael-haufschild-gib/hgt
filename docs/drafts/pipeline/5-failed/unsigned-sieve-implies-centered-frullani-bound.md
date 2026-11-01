# An unsigned factor-two envelope does not imply a centered Frullani bound

- **Stage:** 5-failed
- **Retired claim:** A factor-two upper envelope and mean-one normalization preserve the signed Frullani cancellation needed by Argon §4.1.
- **Scope:** This inference only. The actual signed prime-pair conjecture remains open.

`frullani_factorTwo_meanOne_counterexample` gives a smooth density in `[0,2]`
with exact mean one on every period and bounded discrepancy on every interval,
but unbounded centered signed Frullani integral. The even version retains
the obstruction on positive lags.
More strongly, `frullani_near_one_counterexample` proves this for every fixed
positive tolerance `|a−1|≤ε`, with ordinary discrepancy bounded by `3ε/2`.

**Positive survivor:** The family `a_t=1+t(sin2u−sin u)/2` has unique logarithmic
residue `t/2`, with remainder at most `3|t|`. A bounded primitive of the
phase-weighted numerator after subtracting its mean supplies the general residue bound.
The missing invariant is the mean of `(a−1)(sin2u−sin u)`, not the ordinary mean of `a−1`.

Paper proof and all eleven Lean theorems are complete in the
[formalized card](../3-formalized/frullani-sieve-phase-resonance.md).
Production leaf, standard-axiom audits, and umbrella wiring pass.
