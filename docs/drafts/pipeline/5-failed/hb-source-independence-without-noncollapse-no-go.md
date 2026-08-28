# HB source independence without noncollapse no-go

Status: failed/retired
Route: HB
Closed: 2026-08-28

## Proposed route

Require only that the Peierls response correction be one scalar independent of the Xi divisor, then
deduce RH from universal corrected-current stationarity.

## Exact obstruction

The identically zero fixed response cancels every corrected current without detecting any Xi zero.
HC20 proves this is the only obstruction:

`(∀ q, sourceIndependentCurrent(n,c,q)=0) ↔ c=0 ∨ RH`.

Therefore source independence alone is insufficient unless physical construction also proves
response noncollapse.

## Positive survivor

Every nonzero fixed scalar response preserves full RH force. Pointwise, its current vanishes exactly
on the critical wall; globally, universal stationarity is equivalent to RH. Unit response Ward is
also exactly equivalent to HC18 canonical optical darkness.

This survivor is dependency-closed and formalized in
`ThetaCuspHawkingBMSourceIndependentResponseDichotomy.lean`.

## Lean status

- Exact factorization: `d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_mul`
- Local classification: `d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff`
- Global classification: `forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff`
- Premise-free unit endpoint:
  `forall_d4BMXiSecondHarmonicSourceIndependentUnitResponseCurrent_eq_zero_iff_rh`
- Optical identification:
  `d4BMXiSecondHarmonicSourceIndependentUnitWard_iff_canonicalOpticalWard`
- Target build passed; axiom audit contains only Lean/mathlib foundational axioms

## No-go conclusion

Retire unqualified source independence as a closure principle. Continue only with a literal
action/Green/QNM derivation that proves its fixed response scalar is nonzero.
