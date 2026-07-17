# Genuine meromorphic exponential gauges are differentially algebraic

- **ID:** `meromorphic-exponential-gauge-differential-algebraicity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent theory:** elementary differential algebra and the first-order equation `y' = a*y`
- **Statement:** Every global meromorphic clock gauge `z ↦ exp(lambda*z)` is differentially algebraic over `C(z)`; its differential-algebraic status is discharged internally rather than assumed by downstream Gamma-product classifiers.

## Goal

Close the elementary-gauge hypothesis shared by exact Gamma-valued observables in thermal QFT,
black-hole holography, scattering, and the centered zeta completion.  The result isolates the
non-elementary observability structure: an exponential readout cannot create or erase an HT Gamma
source when it is nonzero.

## Gates

- [x] 0 → 1  in-progress: missing concrete meromorphic exponential DA certificate identified
- [x] 1 → 2  fully-proven: finite-jet first-order constraint and analytic derivative identity complete
- [x] 2 → 3  formalized: exact target, direct file, and standard-only axiom audit pass
- [ ] 3 → 4  publication-ready: not a standalone publication claim

## Exact relation

For the genuine global meromorphic element `E_lambda`,

`E_lambda' = lambda * E_lambda`.

The polynomial finite-jet relation `X_1 - lambda*X_0 = 0` is nonzero, so `E_lambda` is DA over
`C(z)`.  This is a static constraint on the observable.  It asserts no existence, uniqueness, or
temporal propagation theorem.

## Corpus consequences

- The exponential prefactors in the thermal-CFT response can be restored without changing the
  exact half-integral conformal-weight boundary.
- The `pi^(2*w)` factor can be joined to the centered zeta reflected-Gamma quotient inside the same
  meromorphic differential field.
- Any later Gamma-product theorem whose only open gauge premise is a nonzero linear exponential can
  discharge that premise with this module.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA`

- `HTGeometry.differentialAlgebraicOver_of_deriv_eq_base_mul`
- `analyticSubringDeriv_physicalExponentialAnalytic`
- `physicalExponentialMero_deriv`
- `differentialAlgebraicOver_physicalExponentialMero`

Verification:

- `lake build +GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA`
- `lake env lean GaloisForLFunctions/HTGeometry/MeromorphicExponentialGaugeDA.lean`
- `#print axioms` for all four theorems: only `propext`, `Classical.choice`, `Quot.sound`

## Significance verdict

This is not new differential algebra.  Its value is hypothesis discharge and theorem connection:
it converts two existing core-only physics classifications into complete exponential-dressed
observable classifications without adding a new analytic assumption.
