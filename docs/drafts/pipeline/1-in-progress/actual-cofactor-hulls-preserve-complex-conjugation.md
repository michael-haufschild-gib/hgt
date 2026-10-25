# Actual cofactor hulls preserve complex conjugation

- **ID:** actual-cofactor-hulls-preserve-complex-conjugation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (Lean completion pending)
- **Parent:** [Q-III](q-iii-escape-state-classification.md)
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

## Status

Exact Lean draft: `/tmp/qiii_actual_conjugate_hull_body.lean`. Pending source
check and transitive axiom audit; no paper-only completion.
