# Critical golden payment is not Wiener closed

- **ID:** biarithmetic-critical-golden-payment-nonclosed
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Critical payment defect](../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** At `goldenCriticalParameter`, explicit finite repairing kernels converge in the actual critical Wiener norm to an unpaid kernel of norm two. Consequently the actual golden paid ideal is not closed.

The inverse-square-root-tail coefficients lift isometrically to the prime-five
Wiener algebra. Their corrected finite truncations have square-summable
partial sums. Their distance to the unpaid limit is exactly
`2/sqrt(N+1)`, which tends to zero. The actual golden payment criterion
identifies every approximant as paid and the limit as unpaid.

Lean: `BiarithmeticGeometry/CriticalGoldenPaymentNonclosed.lean`.
Audited declarations: `norm_criticalUnpaidWiener`,
`criticalFiniteWienerRepair_distance`, `criticalFiniteWienerRepair_tendsto`,
`criticalFiniteWienerRepair_mem_golden_paidIdeal`,
`criticalUnpaidWiener_not_mem_golden_paidIdeal`, and
`not_isClosed_golden_critical_paidIdeal`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/CriticalGoldenPaymentNonclosed.lean`.
- [x] All six transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Umbrella import wired; umbrella not compiled.

The positive finite-repair approximation and its exact norm error are part
of the theorem. Closure identification and continuum-dimensional quotient
claims remain separate obligations.
