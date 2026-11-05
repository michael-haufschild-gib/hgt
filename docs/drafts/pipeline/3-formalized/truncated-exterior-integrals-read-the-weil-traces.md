# Truncated exterior integrals read the Weil traces

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** If an actual precontact Riesz source has endpoint readout `τ`, then `(1/2)∫_d¹u(t)/t dt / √log(1/d) → τ` at that endpoint.

## Proof

For a continuous endpoint profile with `u(t)√log(1/t)→τ`, set
`F(s)=s u(exp(−s²))`. Then `F(s)→τ`. The exact substitution gives
`∫₀ˢr u(exp(−r²))dr=(1/2)∫_{exp(−S²)}¹u(t)/t dt`.
Complex Cesàro convergence and `S=√log(1/d)` prove the assertion.
Both actual normalized endpoint limits supply the premise unconditionally.

## Lean

`CanonicalSystemOfTheWindowTower/TheWeilTracesDetermineTheirTruncatedExteriorIntegrals.lean`:
`truncated_logarithmic_integral_normalized_limit`,
`evalVector_right_truncatedExterior_limit`,
`evalVector_left_truncatedExterior_limit`.

Plain Lean audit passes. Both actual declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into its umbrella.
Identification with the full exterior Gamma response is a separate step.
