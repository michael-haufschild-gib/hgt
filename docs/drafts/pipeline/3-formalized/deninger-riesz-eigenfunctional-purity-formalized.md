# Riesz-eigenfunctional purity formalized

- **ID:** `deninger-riesz-eigenfunctional-purity-formalized`
- **Stage:** 3-formalized
- **Type:** LEAN 4 THEOREM
- **Label:** `DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY_LEAN`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerArithmeticRieszEigenfunctionalPurity`

## Formalized statement

`deningerClosedWeightOne_rieszEigenfunctional_re_eq_half`:
for a `DeningerClosedWeightOnePolarization`, if a nonzero vector in
the closed generator domain represents a transpose eigenfunctional
with character \(\rho\), then
\[
 \operatorname{Re}\rho=\frac12.
\]

This is the exact abstract bridge from Hodge-norm/domain Riesz
faithfulness of Meyer's order-zero evaluation functionals to the
critical line.

`DeningerClosedWeightOneRieszXiSpectrum` packages one such nonzero
domain representative for every nontrivial Xi-divisor point.
`riemannHypothesis_of_closedWeightOne_rieszXiSpectrum` proves RH from
that package and the closed weight-one polarization.

## Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/DeningerArithmeticRieszEigenfunctionalPurity.lean`
- Result: passed.
- Scratch `#print axioms`: only Lean/mathlib standard `propext`,
  `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.
- No `lake build` was run; final module build is reserved for final
  audit.

## Log

- 2026-07-27 — Formalized transpose-eigenfunctional purity on the
  closed weight-one Hodge generator domain.
