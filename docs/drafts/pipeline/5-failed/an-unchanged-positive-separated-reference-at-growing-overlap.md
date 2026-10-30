# An unchanged positive separated reference at growing overlap

- **ID:** an-unchanged-positive-separated-reference-at-growing-overlap
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement rejected:** The separated Ramanujan reference remains positive at all
  positive overlaps without new overlap terms.

## Obstruction

For every conductor `m≠1`, its continued reference energy is exactly
`E_m(1)-log c`. It is negative precisely when `c>exp(E_m(1))`.
Every finite family of nonpolar conductors is simultaneously negative at a sufficiently
large overlap. This concerns the reference formula, not the actual complete matrix sign.

## Positive survivor and exact insight

The exact scalar decomposition and per-conductor crossing classify the entire positive
and negative reference ranges. The actual archimedean self-error is bounded by
`(exp(1/2)/2)c/N` throughout `0<c≤N`, without a separation assumption.
Thus new interactions, rather than a separation-dependent self-energy error, must account
for any positivity beyond the reference crossing.

## Proof status

The dependency-closed paper arguments are formalized in
`RenormalizedArithmeticPotentialTheory/OverlapForcesNewRamanujanTerms.lean`:
`completeWeilAdjunctionEnergy_neg_iff`,
`exists_overlap_all_nonpolar_reference_energies_negative`, and
`abs_completeWeilSelfError_le_of_width_le_one`.
Final direct check and all three transitive axiom audits passed with default limits.
The only axioms are `propext`, `Classical.choice`, `Quot.sound`.
