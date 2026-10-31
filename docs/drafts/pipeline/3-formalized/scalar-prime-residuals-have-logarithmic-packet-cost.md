# Scalar prime residuals have logarithmic packet cost

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md);
  [packet tails](conductor-packet-quotient-tails-cost-only-logarithms.md).

For `F(n)=sum_(m≤Q)a_m u_m(n)`, one absolute `C>0` satisfies,
for every `Q,N≥2` and every real packet,

`sum_(n≤N)[A(floor(N/n))+log n−log N+gamma]² F(n)²/(n log N)`
`≤C(1+log Q)sum a_m²/log N`.

## Proof

The actual scalar remainder is bounded by the common Mertens profile.
Its proved inverse-logarithmic envelope is dominated in square by
`2C₀² w_N(n)`, where
`w_N(n)=[1+(log(n/N)/(2pi))²]⁻¹`.
On `1≤n≤N`, this weight increases to one. Its scalar harmonic sum is
at most `1+2pi²`, by the existing Wiener-kernel bound.

Every packet Gram differs from its scalar harmonic mass by at most
`2L_Q sum a_m²`, where `L_Q=6log Q+log4+5`.
Discrete Abel summation therefore bounds the weighted discrepancy by
`4L_Q sum a_m²`. Thus one may take
`C=2C₀²(33+2pi²)`, using `L_Q≤8(1+log Q)`.

More generally, every nonnegative increasing weight bounded by one has
packet harmonic discrepancy at most `32(1+log Q)sum a_m²`.
Clipping `w_N` outside `1≤n≤N` applies this statement without changing its
horizon values.

This gives a common norm estimate for the scalar prime residual on
every subpower conductor range. The
[full prime residual](prime-dilation-square-energy-is-the-conductor-adjunction.md)
has cubic logarithmic conductor cost. The complete Weil residual remains separate.

## Lean

`SuccessorShellArithmetic.Conductor.ScalarPrimePacketNorm` proves
`abs_harmonicPacket_monotone_weight_le` and
`exists_scalarPrimeResidual_packet_sq_le`.
Direct production audit passed. Both dependency closures contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
