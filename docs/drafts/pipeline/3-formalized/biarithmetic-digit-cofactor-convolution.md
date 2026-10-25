# Prime-five cofactor packets are digit convolutions

- **ID:** biarithmetic-digit-cofactor-convolution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../1-in-progress/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** Every signed prime-five cofactor packet is exactly the digit row of a causal geometric convolution.

## Exact identity

Put `C_a(f)_l=sum_(r<=l) a^(l-r) f_r`. Dividing an integer by `5^r`
removes precisely its first `r` base-five digits. Thus finite triangular
reindexing gives, for every natural `n`,

`W_(C_a(f))(n)=sum_(r<=log_5(n)) f_r D_a(floor(n/5^r))`.

This identity includes zero and arbitrary signed coefficients, with no
convergence condition. When `a` is nonzero the coefficient is exactly
`a^l sum_(r<=l) f_r/a^r`. Combining this statement with the digit-energy
domain identifies the packet's weighted partial-sum criterion. Its comparison
with actual convolution payment also requires the paid mean-correction theorem.

## Verification

Lean: `BiarithmeticGeometry/DigitCofactorConvolution.lean`.
Declarations: `fiveTruncatedDigitReadout_convolution`,
`fiveWeightedDigitRow_convolution`, `finiteGeometricConvolution_eq_partialPoleSum`.

- [x] Finite paper proof and exact natural cutoff.
- [x] Direct repository leaf check; umbrella import wired.
- [x] Three transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
