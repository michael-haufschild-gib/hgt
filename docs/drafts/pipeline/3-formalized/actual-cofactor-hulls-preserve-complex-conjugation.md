# Actual cofactor hulls preserve complex conjugation

- **ID:** actual-cofactor-hulls-preserve-complex-conjugation
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Statement:** Every actual cofactor annihilator and its module hull are
  invariant under coefficient and character conjugation, respectively.

## Exact route

All source rows are real. Conjugating Wiener coefficients therefore
conjugates the complete finite-cell source row and its pairings. The
already proved common-subsequence pairing limit gives the same identity
for cyclic Hilbert vectors, hence equality of their norms. A Wiener
element annihilates the module exactly when its cyclic vector vanishes,
so coefficient conjugation preserves the annihilator. The existing
`TheCalculusOfTheObstructionHull.bohrEval_conj` then transports hull points.

This is a statement about each actual limiting module, distinct from the
existing conjugation symmetry of the full paid obstruction hull. It does
not identify module characters with zeta zeros or exclude real characters.
An even zero-count or paired multiplicity formula is not inferred from
set symmetry alone.

## Lean verification

Canonical module:
`ArithmeticDefectRigidity/ActualCofactorHullsRespectConjugation.lean`.
Scratch retry `19444` and final canonical source-only check `78866` passed.
The module is umbrella-wired; no olean was needed for a written importer.
Transitive axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

- `complexWienerRow_conj` and `wienerSourcePairing_conj`: exact finite-source
  conjugation identities.
- `ActualCofactorLimit.inner_wiener_conj` and `norm_wiener_conj`: limiting
  cyclic inner products and norms.
- `ActualCofactorLimit.conjW_mem_annihilator_iff`: coefficient-conjugation
  invariance of the complete annihilator.
- `ActualCofactorLimit.conj_mem_moduleHull`: conjugation symmetry of each
  actual module hull.
