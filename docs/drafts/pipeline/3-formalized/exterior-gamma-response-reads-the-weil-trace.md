# Exterior Gamma response reads the Weil trace

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At either endpoint of every actual precontact Weil Riesz source, the exterior Gamma response divided by `√log(1/d)` tends to minus its normalized endpoint readout. The literal integral is almost everywhere the negative of the actual bounded Gamma boundary transfer.

## Proof

For a bounded continuous endpoint profile `u`, compare the displaced kernel
`exp(−(t+d))/(2(t+d))` with `1/(2t)` truncated to `[d,1]`.
Splitting at `d` and `1` bounds the error by `(2+R)‖u‖∞` on `[0,R]`.
The exact Gamma remainder is at most `3/4`, so its additional integral is
bounded by `3R‖u‖∞/4`. Division by `√log(1/d)` removes both errors.
The proved truncated-integral limit gives the coefficient. Compact support
reduces the actual half-line transfer to the same finite integral.

## Lean

`CanonicalSystemOfTheWindowTower/TheWeilTracesDetermineTheirExteriorGammaResponse.lean`:
`logarithmicExteriorIntegral_sub_principal_bound`,
`gammaExteriorIntegral_sub_principal_bound`,
`evalVectorRightExteriorResponse_eq_boundaryTransfer`,
`evalVectorLeftExteriorResponse_eq_boundaryTransfer`,
`evalVectorRightExteriorResponse_normalized_limit`,
`evalVectorLeftExteriorResponse_normalized_limit`.

Plain Lean audit passes; all six declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Wired into the programme umbrella.
Scaled L² convergence and the full collar equation remain separate steps.
