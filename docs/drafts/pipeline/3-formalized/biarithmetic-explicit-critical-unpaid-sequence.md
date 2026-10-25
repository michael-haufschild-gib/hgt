# An explicit boundary sequence for critical payment

- **ID:** biarithmetic-explicit-critical-unpaid-sequence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; normalized coefficient calibration)
- **Parent:** [Critical payment defect](../2-fully-proven/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** An explicit real sequence has absolute sum two and total sum zero, but divergent squared partial sums. Finite zero-sum repairs have finite partial-sum energy and approach it at exact coefficient distance `2/sqrt(N+1)`.

## Proof

Put `u_n=1/sqrt(n+1)`, `g_0=-1`, and `g_(n+1)=u_n-u_(n+1)`.
The tail is positive, decreasing, and tends to zero. Telescoping gives
`sum_(r<=M) g_r=-u_M` and `sum_(r<=M)|g_r|=2-u_M`.
Thus the absolute sum is two, the signed sum is zero, and the squared partial
sums form the divergent shifted harmonic series.

For each `N`, keep coefficients through `N`, add `u_N` to the constant
coefficient, and set later coefficients to zero. Every partial sum from
`N` onward vanishes, so the repair has finite square energy. Its distance
from `g` is the constant correction plus the omitted positive tail, exactly
`2u_N`, which tends to zero.

## Scope and verification

This theorem concerns normalized coefficient sequences. Transfer to the actual
golden Wiener ideal and the continuum-dimensional quotient are separate
statements. No closedness of payment is assumed.

Lean: `BiarithmeticGeometry/CriticalUnpaidSequence.lean`.
Main declarations: `criticalUnpaidCoeff_partialSum`,
`tsum_abs_criticalUnpaidCoeff`, `tsum_criticalUnpaidCoeff`,
`not_summable_sq_criticalUnpaidCoeff_partialSum`,
`summable_sq_criticalFiniteRepair_partialSum`,
`criticalFiniteRepair_distance`, `criticalFiniteRepair_tendsto_distance`.

- [x] Dependency-closed paper proof.
- [x] Direct repository source check; umbrella import wired.
- [x] Seven transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
