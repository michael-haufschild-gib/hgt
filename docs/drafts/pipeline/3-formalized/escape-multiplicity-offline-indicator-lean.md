# The escape multiplicity is the off-line indicator (audit of the direct sub-unit anchor)

- **ID:** DSA-AUDIT-LEAN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), audit of `1-in-progress/universal-law-field/direct-subunit-anchor/`
- **Statement:** `thetaKakutaniEscapeMultiplicity q = if Re q = ½ then 0 else 1` for every Xi
  divisor copy; the fusion's sub-unit gap `budget < (115/108)·multiplicity` holds at a copy
  exactly when the copy is off the line; the multiplicity vanishes at every copy exactly when RH
  holds.

## Reading
The integer of the corpus's Ferrero–Washington-shaped anchor is the indicator of the conclusion's
failure, and the only "bound below one unit" available for it (the trace-capacity law) is
RH-equivalent (`routePPrimitiveCollisionTraceCapacityLaw_iff_riemannHypothesis`). A genuine direct
anchor needs an integer defined independently of the zero's position whose positivity is forced
by an off-line zero and whose bound is proved by an independent estimate; the escape multiplicity
is not such an integer. The programme's proposed "prime-mixed formation strictness" has no formal
statement yet; any version of it that implies the capacity law is RH-strength.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.EscapeMultiplicityOffLineIndicator` | `thetaKakutaniEscapeMultiplicity_eq_zero_iff_re_eq_half`, `thetaKakutaniEscapeMultiplicity_eq_one_iff_re_ne_half`, `thetaKakutaniEscapeMultiplicity_eq_ite`, `budget_lt_quantum_mul_escapeMultiplicity_iff`, `forall_thetaKakutaniEscapeMultiplicity_eq_zero_iff_riemannHypothesis` |

Inputs: `thetaKakutaniEscapeMultiplicity_eq_zero_iff`,
`thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero`,
`primeDepthBVWoldXiCenteredRate_eq_zero_iff`, `routePPrimitiveCollisionCubicTraceBudget_lt_quantum`,
`routePPrimitiveCollisionCubicTraceBudget_nonneg`, `nonempty_xiRightZeroCopy_of_not_riemannHypothesis`,
`xi_eq_zero_of_mem_divisor_support`, `xi_zero_re_eq_half_of_riemannHypothesis`. Axioms:
`propext, Classical.choice, Quot.sound`. Wired into `GaloisForLFunctions.RHTower`.

## Log
- 2026-09-02 — created at stage 3.
