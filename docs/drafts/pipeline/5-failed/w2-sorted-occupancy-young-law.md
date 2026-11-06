# Sorted occupancy does not give the Young coherent law

- **ID:** w2-sorted-occupancy-young-law
- **Stage:** 5-failed
- **Type:** FALSIFIED / POSITIVE CHARACTER SURVIVOR
- **Source:** [W2 construction](../1-in-progress/w2-representation-construction.md).
- **Statement:** Sorting independent-letter multiplicities does not produce Schur–Weyl branching, except for a single supported color.

## Exact obstruction

For nonnegative finite letter weights put
`R = Σ_(a≠b) w_a² w_b`. The occupancy mass of `(2,1)` is `3R`.
The dimension-weighted Young down-transition sends half this mass to `(2)`, so

`mass(3) + mass(2,1)/2 − (Σw) mass(2) = R/2`.

Moreover `R=0` iff every pair of distinct letters includes a zero-weight letter.
Thus this branching equation fails for every probability alphabet with at least two supported
colors. Following Young-graph edges at the level of partitions is insufficient.

## Positive survivor

Retain the independent word and use the probability that a permutation fixes every letter.
Its finite Gram matrices are sums of nonnegative stabilizer kernels. A cycle of length `k`
forces its letters equal and contributes `Σw^k`; disjoint cycles multiply. Total letter mass
one gives identity value one and restriction coherence. Summable alphabets satisfy the same
identities by absolute convergence.

This is the classical independent-color character. It supplies a correct positive representation
model without claiming that sorted occupancy gives its irreducible multiplicities. Identifying
arithmetic cycle values with this model remains a separate obligation.

## Formal certificate

- `MultiplicityBranching.lean`: `hookContentMass_eq`, `content_young_branching_defect`,
  `repeatedLetterMass_eq_zero_iff`.
- `CountableColoring.lean`: `wordCharacter_posSemidef`, `wordCharacter_optionCongr`.
- `CycleCharacterIdentification.lean`: `wordCharacter_eq_cycleMomentCharacter`,
  `wordCharacter_positiveCycleFamily`.

All modules lie in `formal/GaloisForLFunctions/HTGeometry/SymmetricCharacters/` and are
kernel-checked. The obstruction and positive survivor have dependency-closed proofs.
