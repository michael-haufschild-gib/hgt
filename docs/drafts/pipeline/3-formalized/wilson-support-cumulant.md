# Wilson support-order cumulant law

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [LEAN PROVED] [STRENGTHENED]`

Source: Section 7 of *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163).

## Exact claim

For any finite weighted family, the Möbius inversion of moments restricted to subsets of `S`
equals exactly the total weight of members whose support is `S`. Hence arbitrary weights on words
of length `r` have zero genuine-support cumulant on every vertex set with more than `r` elements.

Closed Wilson walks are obtained by assigning zero weight to nonclosed words and the desired trace
weight to closed words. Their support cumulants therefore vanish above walk length exactly, with no
positivity or matrix-dimension assumption.

## Strength over source statement

The source derives the vanishing law from a block-matrix trace expansion. The formal result isolates
the universal combinatorial mechanism: it works over every commutative ring, for arbitrary finite
weighted objects, and proves exact-support extraction before specializing to Wilson words.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/WilsonSupportCumulant.lean`, headline declarations
`supportMobiusCumulant_eq_supportLayer` and `wilsonWalkSupportCumulant_eq_zero`. The word-length
support bound is proved internally by `walkSupport_card_le`; large support is packaged as a subtype,
so the vanishing theorem has no external premise and introduces no axioms.
