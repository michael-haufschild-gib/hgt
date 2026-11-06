# Finite unmarked partition stabilizers fail restriction

- **ID:** w2-unmarked-finite-partition-stabilizers
- **Stage:** 5-failed
- **Type:** FALSIFIED / BLOCKWISE CHARACTER SURVIVOR
- **Source:** [W2 construction](../1-in-progress/w2-representation-construction.md).
- **Statement:** Unmarked independent-color partition stabilizers are positive and central at each rank, but coherent only for one supported color.

## Exact obstruction

Let `R = Σ_(a≠b) w_a² w_b` and `s = Σw`. Every partition of two positions is
preserved by their exchange. After adding a fixed third position, preservation fails when
its color matches exactly one exchanged position. Hence

`s χ₂((12)) − χ₃((12)) = 2R`.

The defect vanishes iff at most one color has positive weight. Positivity and centrality at
each rank therefore do not suffice for restriction coherence.

## Positive survivor and limit mechanism

Fix each block individually. This is exactly the fixed-word event, so its probability is
the independent-color character: positive, central, and restriction-coherent when `s=1`.

On any set whose occupied color blocks are all infinite, a finitely supported permutation
preserves the unmarked partition iff it fixes every color. Indeed, if a block moves, every
point in that block must move, putting an infinite block inside finite support. Thus the
infinite-block stabilizer has precisely the correct blockwise condition; taking stabilizers
of finite restrictions loses this rigidity.

## Formal certificate

`formal/GaloisForLFunctions/HTGeometry/SymmetricCharacters/PartitionStabilizers.lean`:

- `partitionCharacter_posSemidef`, `partitionCharacter_conj`.
- `partitionCharacter_restriction_defect`, `partitionCharacter_restriction_eq_iff`.
- `blockwisePartitionCharacter_eq`, `blockwisePartitionCharacter_restriction`.
- `partition_fixed_iff_of_infinite_blocks`.

The obstruction and both positive survivors have dependency-closed paper proofs and pass
direct Lean leaf checking. No claim of a new classification theorem or arithmetic producer.
