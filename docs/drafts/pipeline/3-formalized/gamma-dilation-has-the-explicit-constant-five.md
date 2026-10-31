# Gamma dilation has the explicit constant five

- **Stage:** 3-formalized
- **Programme:** A10
- **Lean:** `ArithmeticIncidencePositivity/GammaDilationHasAnExplicitConstant.lean`; direct Lean and transitive axiom audits passed.

For every `r>0` and real `t`,
`|γ(rt)−γ(t)|≤5|log r|`.

The trigamma series on `Re z=1/4` has norm at most twenty. Indeed, with
`a=n+1/4`, each term has norm at most `1/a²≤5(1/a−1/(a+1))`.
Finite sums telescope, and the proved trigamma limit gives the bound.
Thus `|γ′(t)|≤5` for all real `t`. On `0<t≤1`, this bounds `t|γ′(t)|`
by five. On `t≥1`, the existing vertical estimate gives
`t|γ′(t)|≤1/t+π/4<5`.

The derivative of `u↦γ(exp u)` is consequently bounded by five. The
mean-value inequality proves the logarithmic modulus on positive frequencies;
evenness and the value at zero cover the full line. No compactness constant
or numerical estimate is needed.

Caps: `norm_deriv_digamma_quarter_le` and
`gammaHardyPhaseRate_logarithmic_dilation_bound`. Both depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.
