# Uniform finite square-sum bounds for geometric convolution

- **ID:** biarithmetic-finite-geometric-convolution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** For every real sequence `u`, every `0<=q<1`, and every horizon `R`, causal geometric convolution satisfies `(1-q)^2 sum_(M<=R) C_q(u)_M^2 <= sum_(M<=R) u_M^2`.

## Exact finite proof

Define `C_q(u)_M=sum_(l<=M) q^(M-l)u_l`. Its recurrence is
`C_q(u)_(M+1)=q C_q(u)_M+u_(M+1)`. Summing the recurrence gives

`(1-q) sum_(M<=R) C_q(u)_M = sum_(M<=R) u_M-q C_q(u)_R`.

For the constant sequence, induction gives `(1-q)C_q(1)_M<=1`.
Weighted Cauchy--Schwarz then gives

`(1-q)C_q(u)_M^2 <= C_q(u^2)_M`.

Sum this inequality, multiply by `1-q`, and use the exact mass identity on
`u^2`. Its endpoint term is nonnegative, proving the claimed horizon-uniform
bound. No infinite convolution or summability premise is needed. This is the
classical geometric Young estimate, retained in a fully finite form for the
pronic digit-energy comparison.

## Verification

Lean: `BiarithmeticGeometry/FiniteGeometricConvolution.lean`.
Main declarations: `finiteGeometricConvolution_succ`,
`finiteGeometricConvolution_sum`, `finiteGeometricConvolution_sq_le`, and
`sum_sq_finiteGeometricConvolution_le`.

- [x] Dependency-closed paper proof.
- [x] Direct repository source check and umbrella import.
- [x] Four transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
