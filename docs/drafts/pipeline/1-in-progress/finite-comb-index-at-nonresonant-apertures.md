# Exact comb index at nonresonant apertures

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A94; complement to the robust-margin index law.

## Missing step

A robust-index bound does not control negative eigenvalues tending to zero.
For the raw comb, retain a small negative mass shift in the continuum
comparison and bound the shifted continuum index.

## Available mechanism

`negativeRank_add_nullity_le_of_aperture_lt` proves that every null mode
becomes additional negative dimension on every strict aperture enlargement.
`finite_resonant_apertures_below` therefore leaves nonresonant apertures
between any two fixed endpoints.

At a nonresonant aperture, the restricted Weil operator is identity minus
compact and has a spectral gap at zero. A sufficiently small positive
energy shift preserves its finite negative rank. Block averaging with
errors charged only to block means should transfer every raw negative comb
subspace injectively into this shifted continuum form. Sampling supplies
the reverse inequality for interior negative packet families.

For a finite global index `k`, once an aperture contains `k` negative
directions it cannot have a null mode: every larger aperture still has
index at most `k`. Thus this route should identify the eventual raw comb
index on sufficiently large fixed windows, without assuming a spectral gap.

## Lean status

Null-mode growth and finiteness of resonant apertures are existing proved
results in `ArithmeticContinuationAndCriticalEnergy/NullModesForceApertureIndexGrowth`.
`NonresonantWeilIndexSurvivesPositiveEnergyShifts`,
`FiniteSmoothWeilGramsAndRestrictedIndex`, and
`TightBlockTransferSpendsOnlyMeanMass` supply the shared candidate bridges;
their status is recorded in `unshifted-comb-index-at-nonresonant-ratios.md`.
The last transfer retains the shift `B(packetForm−η Σ blockMean²)≤combForm`
and loses only `1/R` in window ratio. A negative comb direction cannot
have zero block image.

`HodgeTheoryOfAFixedPart/TheApertureIndexCountsNoExtraZeros` uses smooth
index capture and transpose invariance to obtain
`negativeRank(a,0)≤#rightZeros`. An aperture attaining the finite global
index therefore has no null mode. Its direct Lean check is pending.
The shifted step-packet index bound and exact raw-index conclusion remain open.
