# Degree rotation on the Laurent central extension

- **Stage:** 1-in-progress
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](garland-loop-eisenstein-over-q.md)
- **Target:** An actual action of `Fˣ` on `LoopSL2 F` induced by `X↦qX`, fixing
  the center, with the expected action on each affine real-root subgroup.

## Sources and dependency audit

Liu, *Eisenstein Series on Loop Groups*, §3.1,
<https://arxiv.org/abs/1103.4212>, uses this rotation and its semidirect product.
The corpus already constructs `quantumLaurentScaleAut` and
`quantumLaurentScaleHom` coefficientwise in `SkewLaurentCoefficientTrace.lean`.
Their support identity and the proved Laurent valuation/coefficient criterion
supply the required valuation compatibility. The completed rank-one symbol
construction supplies the central extension; its cocycle is not an assumption.

## Dependency-closed paper proof

For `q∈Fˣ`, define `σ_q(∑a_nX^n)=∑q^n a_nX^n`. The existing coefficientwise
construction proves it is a field automorphism, with inverse `σ_(q⁻¹)` and
`σ_qσ_r=σ_(qr)`. Nonzero scalar multiplication preserves exactly the vanishing
coefficients. The Laurent valuation criterion
`v(f)≤D ⇔ all coefficients below -log D vanish` for `D≠0` therefore proves
`v(σ_q f)=v(f)`, handling `f=0` separately.

For any element of the Laurent valuation ring, choose its power-series
representative. The canonical residue equivalence is its constant coefficient.
Since `σ_q` fixes coefficient zero, the residue of every valuation-zero unit
is unchanged. In the tame symbol, the zero-valuation unit
`(-1)^(mn) a^n b^(-m)` is sent to the identical expression with `a,b` replaced
by their images, because their integer valuations `m,n` are unchanged.
Thus `T(σ_q a,σ_q b)=T(a,b)`.

Apply `σ_q` to all four entries of a determinant-one matrix. This gives a group
automorphism. Injectivity of the field map implies
`x(σ_q g)=σ_q(x(g))`, including the triangular branch. Hence the multiplicative
Kubota tame cocycle is unchanged. The map `(g,u)↦(σ_q g,u)` is therefore a
group automorphism of the actual central extension. Its inverse and composition
laws follow entrywise from those of `σ`; the center is fixed.

On a root matrix with off-diagonal entry `aX^n`, the action replaces `a` by
`q^n a`. This agrees with the affine degree label. Over `ℝ`, set
`q=exp(-exp(r))`; then `0<q<1` and every positive rotation magnitude `exp(r)`
is covered. The resulting automorphism supplies the actual degree rotation
corresponding to the already proved weight exponent.

## Status

Paper proof complete; Lean formalization pending. No Iwasawa, arithmetic-series,
or constant-term theorem is claimed by this construction.
