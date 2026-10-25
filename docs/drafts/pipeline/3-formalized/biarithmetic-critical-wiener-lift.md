# Isometric real coordinates on the critical prime-five algebra

- **ID:** biarithmetic-critical-wiener-lift
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; actual Wiener embedding)
- **Parent:** [Critical payment defect](../2-fully-proven/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** Normalized real coefficients lift to actual critical Wiener kernels with exact coefficient mass and distances. Their payment for the critical tower is exactly square summability of their coefficient partial sums.

## Proof

For a real sequence `g` with summable absolute values, define
`k(5^r)=sqrt(5)^r g_r` and set all other coefficients to zero.
The identity `sqrt(5)^r (5^r)^(-1/2)=1` cancels the actual Wiener weight.
Injectivity of the five-power map reindexes the supported series, giving
`||k||_W=sum_r|g_r|`. Applying the same identity to differences gives
`||k_g-k_h||_W=sum_r|g_r-h_r|`.

The lift uses AOT's existing real-kernel embedding. Its imaginary part
vanishes, and its real part is the exact tower-supported row. The checked
critical tower criterion therefore identifies membership in the actual
complex paid ideal with summability of
`(sum_(r<=M)g_r)^2`.

## Scope and verification

The coefficient-mass identity holds even without summability; constructing
an actual Wiener element requires exactly its defining absolute-sum
condition. Complex linearity, golden nonclosedness, and continuum quotient
dimension are separate statements.

Lean: `BiarithmeticGeometry/CriticalWienerLift.lean`.
Main declarations: `tsum_abs_fiveCriticalKernelLift`,
`norm_fiveCriticalWienerLift`, `norm_fiveCriticalWienerLift_sub`,
`mem_paidIdeal_critical_fiveCriticalWienerLift_iff`.

- [x] Dependency-closed paper proof.
- [x] Direct repository source check; umbrella import wired.
- [x] Four transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
