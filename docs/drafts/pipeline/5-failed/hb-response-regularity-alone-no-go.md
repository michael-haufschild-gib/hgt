# HB response regularity alone no-go

Status: failed/retired
Route: HB
Closed: 2026-08-28

## Proposed route

Exclude the earlier punctured-height Peierls response countermodel by requiring a division-free
response correction regular at the critical source wall. Then infer that universal corrected
reflection-current stationarity still forces RH.

## Exact obstruction

HC19 constructs the explicit division-free correction

`K_n(q) = (2q-1) F_n(reflect q)`

from the literal bare radial response factor `F_n`. Its corrected charge is

`H_n(q) = (2q-1) F_n(q) F_n(reflect q)`.

Functional-equation involution makes `H_n` reflection-odd, so the corrected current cancels on
every Xi fibre unconditionally. Both `K_n` and `H_n` vanish exactly on the critical wall. For every
tilted Xi copy, `H_n` is nonzero and HC18 canonical optical power is strictly positive.

Therefore division-freeness, wall regularity, correct wall vanishing, and nontrivial off-wall
response together do not recover RH force.

## Positive survivor

The obstruction isolates the missing physical gate: response must be independent of the source it
acts on, reflection-local, or derived from a literal left-QNM/action incidence. Merely prescribing
regularity or the wall zero locus cannot exclude source-matched reflected factors.

This survivor is dependency-closed and formalized in
`ThetaCuspHawkingBMCrossPairResponseCompensator.lean`. Its strongest endpoint proves nonzero
off-wall charge, zero corrected current, and positive canonical optical power in one conjunction.

## Lean status

- Exact factorization: `d4BMXiSecondHarmonicCrossPairResponseCharge_eq`
- Exact zero locus: `d4BMXiSecondHarmonicCrossPairResponseCharge_eq_zero_iff`
- Oddness/cancellation: `d4BMXiSecondHarmonicCrossPairResponseCharge_reflection_odd` and
  `forall_d4BMXiSecondHarmonicCrossPairResponseCorrectedReflectionCurrent_eq_zero`
- Nontriviality certificate: `d4BMXiSecondHarmonicCrossPairCancellation_nontrivial_of_tilt`
- Target build passed; axiom audit contains only Lean/mathlib foundational axioms

## No-go conclusion

Retire response regularity alone as an HB closure principle. Continue with exact
source-independence/reflection-locality classifications and an action-derived response map.
