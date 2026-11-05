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
Finite prime translations of the continuous source and the two exact
exponential polar profiles are continuous. Their scalar, prime, and polar
combination represents the actual bounded remainder on every enclosing
aperture. Subtracting it from the evaluation exponential and exterior Gamma
response gives the full collar profile; its normalized coefficient is `τ`.

For `d=hs`, write `log(1/(hs))=log(1/h)+log(1/s)`. A bounded normalized
response gives the squared majorant `C(1+log(1/s))` on `0<s<1`, which is
integrable. The logarithmic ratio tends pointwise to one. Dominated
convergence therefore gives the scaled L² limit from the scalar boundary
limit alone.

## Lean status

[Normalized actual endpoint traces](../3-formalized/normalized-boundary-traces-of-weil-riesz-vectors.md)
and their [truncated exterior integrals](../3-formalized/truncated-exterior-integrals-read-the-weil-traces.md)
are formalized. The [exact exterior Gamma response](../3-formalized/exterior-gamma-response-reads-the-weil-trace.md),
including its uniform principal-kernel comparison and actual boundary-operator
identification, is also formalized. Scaled L² convergence and the full collar
profile have Lean drafts awaiting audit.
