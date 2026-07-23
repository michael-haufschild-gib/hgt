# Gamma affine-pole energy universality law

- **ID:** gamma-affine-pole-energy-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** cross-folder closure of `GammaPoleAffineSimpleOrderLaw` and `MobiusLaplaceGammaHankelBoundaryPole`
- **Statement:** Exact simple meromorphic order of a moving affine Gamma source at a branch is equivalent to failure of every uniform `L²` energy bound on vertical lines approaching the corresponding boundary principal part; the coefficient is canonical on the at-most-simple horizon.

## Goal

Connect the local algebraic pole classification to the global Hilbert-energy obstruction instead
of leaving coefficient nonvanishing as two unrelated terminal interfaces.

## Gates

- [x] 0 → 1  in-progress: exact Lean statements aligned and prior corpus searched
- [ ] 1 → 2  fully-proven: dependency-closed proof pending exact Lean check
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

The affine Gamma order theorem identifies simple order with nonvanishing of the branch coefficient.
The exact boundary-pole integral shows that zero coefficient gives identically zero line energy,
whereas the existing nonzero-coefficient theorem rules out every uniform bound.  This upgrades the
one-way energy obstruction to an iff and composes it with both the explicit affine-source order law
and the canonical at-most-simple derivative coefficient.

## Audit

- **[CORPUS]:** HTGeometry classifies simple Gamma order by branch-coefficient nonvanishing
- **[CORPUS]:** RHTower proves nonzero boundary coefficient → unbounded line energy
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; neither the energy converse nor the order–energy equivalence appears in corpus
- **Status:** `[LEAN-DEVELOPMENT] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — terminal cross-folder pole/order and Hilbert-energy interfaces aligned
