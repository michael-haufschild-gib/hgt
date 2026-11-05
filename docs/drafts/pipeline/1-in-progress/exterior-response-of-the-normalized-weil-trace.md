# Exterior response of the normalized Weil trace

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** At either endpoint of an actual precontact Weil Riesz source, the exterior logarithmic operator response divided by `sqrt(log(1/d))` tends to minus its normalized trace. After dilation of a closing collar, the normalized response converges in L² to that constant.

## Proposed proof

The continuous source profile `u` is bounded and satisfies
`u(t)sqrt(log(1/t))→τ`. Set `F(s)=s u(exp(-s²))`. Then `F→τ`, so the
complex Cesàro theorem and substitution `t=exp(-s²)` give

`(1/2)∫_d¹ u(t)/t dt / sqrt(log(1/d)) → τ`.

Replacing this kernel by `exp(-(t+d))/(2(t+d))` on the positive half-line
has bounded error. Split at `d` and `1`; boundedness controls the short and
remote pieces and the difference `d/(t(t+d))` controls the middle piece.
The integrable Gamma remainder changes the response by a bounded quantity.
Finite prime translations and polar terms also stay bounded.

For `d=hs`, the trace bound should give the common L² majorant
`C sqrt(1+log(1/s))` on `0<s<1`. Dominated convergence then gives the
scaled exterior forcing needed by the collar Schur formula.

## Lean status

[Normalized actual endpoint traces](../3-formalized/normalized-boundary-traces-of-weil-riesz-vectors.md)
are formalized. The complex
Cesàro theorem is formalized in `HTGeometry/QuasiPolynomialLaplaceCalculus`.
The substitution, uniform kernel-comparison bound, actual exterior-operator
identification and scaled L² limit remain unformalized.
