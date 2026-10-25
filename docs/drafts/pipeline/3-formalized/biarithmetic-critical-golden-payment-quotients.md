# Actual critical golden payment quotients and their cardinality bounds

- **ID:** biarithmetic-critical-golden-payment-quotients
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Critical payment defect](../1-in-progress/biarithmetic-critical-payment-has-continuum-defect.md)
- **Statement:** The actual critical golden paid ideal, its Wiener closure, its closure defect, and its unreduced quotient have canonical complex-linear constructions. Both quotients have Hamel rank at most continuum.

Write `P` for the actual paid ideal and `Z` for its Wiener closure.
Restricting scalars gives the complex subspaces and quotients `Z/P` and
`W/P`, together with their canonical comparison map. No ambient closedness
is assumed. Cardinality of actual Wiener coefficients bounds the cardinality
of each quotient, hence its complex Hamel rank, by continuum.

Lean: `BiarithmeticGeometry/CriticalGoldenPaymentQuotients.lean`.
Audited declarations: `criticalGoldenDefectToQuotient`,
`rank_criticalGoldenPaymentQuotient_le_continuum`, and
`rank_criticalGoldenPaymentClosureDefect_le_continuum`.

- [x] Direct repository check with `lake --old env lean`.
- [x] Umbrella import wired; umbrella not compiled.
- [x] All three transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.

Equality with continuum requires the independent unpaid family; that
stronger claim remains an obligation on the parent card.
