# Xi pairwise valuation-base universality law

- **ID:** xi-pairwise-valuation-base-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** closure of `XiTransverseShiftPairwiseDifferentialRank`, `XiTransverseShiftPairwiseAllValuationRank`, and characteristic-zero base change for the rooted incidence matrix
- **Statement:** Adjoining every scalar prime-valuation layer preserves the entire differential matroid of every finite corrected integral-shift pair-difference packet; hence all selected independence predicates and ranks are base-invariant.

## Goal

Upgrade the corpus's vertex-packet base-invariance theorem to arbitrary oriented pair-difference
packets and from one independence predicate to equality of the complete differential matroid.

## Gates

- [x] 0 → 1  in-progress: exact Lean statements aligned and prior corpus searched
- [ ] 1 → 2  fully-proven: project connector awaits final rebuild of stale pairwise rank dependencies
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

Every rooted incidence matrix is the scalar extension of its rational incidence matrix.  The
finite base-change theorem for linear independence therefore makes its matroid independent of the
chosen characteristic-zero coefficient field.  The two existing Xi rank theorems identify the
rational-coordinate and all-valuation differential matroids with those two coefficient versions
of the same rooted incidence matroid.

## Audit

- **[CORPUS]:** vertex Xi packets have a base-invariance iff, but pair-difference packets do not
- **[CORPUS]:** pair-difference rank modules separately identify both bases with rooted incidence
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; equality of the complete cross-base pairwise differential matroids is absent
- **Status:** `[LEAN-DEVELOPMENT] [GENERIC-CORE-EXACT-LEAN-PASS] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — generic characteristic-zero rooted-incidence equality passed exact Lean check
- 2026-07-22 — project connector deferred: cached pairwise `.olean` files predate current `rootedIncidenceMatroid` parameter list; final module build must refresh them
