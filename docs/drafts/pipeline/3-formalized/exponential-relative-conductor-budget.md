# Exponential relative conductor budget

- **ID:** exponential-relative-conductor-budget
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Σ1d; exponential conductor floors and quadratic quasimode residuals.
- **Statement:** A universal `b>0` gives every nonzero compact real `C²` profile a constant `K>0` such that its summed squared relative conductor residual is bounded by
  `K[(c+1)²exp(2bc)+Q²](1+log Q)²[c²(1+log c)³(log N)^(1/k-1)+c¹⁰(log N/N)²]`,
  eventually for each fixed polylogarithmic conductor ceiling and integer `k≥1`, under the existing geometric width condition.

## Proof

The conductor floor is `E_m≥a exp(-bc/m)`. For `m≤⌈c⌉`, replace it by
`a exp(-bc)`; their conductor weights sum to at most `(c+1)²`.
For `m>⌈c⌉`, the floor is at least `a exp(-b)` and the weights sum to
at most `Q²`. Hence
`Σ_(m≤Q) m/E_m² ≤ a⁻²[(c+1)²exp(2bc)+exp(2b)Q²]`.
Absorb the fixed factors into `K`.

The formalized theorem
`exists_completeWeil_quadratic_conductor_residual_variable_rate` bounds
each squared residual by the displayed rate times `Kφ m(1+log m)²`.
Use `log m≤log Q`, divide by `E_m²`, and sum the preceding weight bound.
All analytic inputs apply to arbitrary compact `C²` profiles, including
profiles with real Fourier zeros.

## Lean

Module: `CriticalArithmeticCorrelationTheory/ExponentialFloorsControlRelativeConductorWeights.lean`.

- `exists_universal_exponential_relative_conductor_weight_bound`
- `exists_universal_exponential_relative_residual_budget`

Direct Lean check passed. Both transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Module wired into its umbrella.

For `c≤α log log N` and `Q≤(log N)^A`, the bound tends to zero whenever
`max(2bα,2A)+1/k<1`. Positivity of the compressed complete form still
requires the relative-frame argument and its Lean proof.
