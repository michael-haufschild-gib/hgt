# Prime–archimedean / black-hole / reciprocal spectral-cone universality

- **ID:** prime-arch-black-hole-reciprocal-spectral-cone-universality
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** cross-folder closure of `BlackHoleReciprocalSpectralConeLaw` and `PrimeArchHankelDeterminantCriterion`
- **Statement:** RH holds exactly when every nonzero nonnegative mixture of the normalized black-hole far-zone clock, reciprocal continuum clock, and normalized prime–archimedean moment clock has positive-definite Hankel matrices at every finite depth; under RH every such mixture escapes all fixed finite spectral and hidden-state dimensions.

## Goal

Adjoin the RH-sensitive prime--archimedean ray to the unconditional two-ray physical strict Hankel
cone and determine the exact resulting cone criterion.

## Gates

- [x] 0 → 1  in-progress: cross-folder strict-Hankel rays aligned from exact Lean statements
- [x] 1 → 2  fully-proven: dependency-closed cone proof and pure-ray converse
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

Under RH, the prime--archimedean Hankel matrix is positive definite in every degree by the Xi
central-moment criterion.  The black-hole and reciprocal matrices are unconditionally positive
definite.  A nonzero nonnegative combination of three positive-definite matrices is positive
definite: select a coefficient that is strictly positive and treat the remaining summands as
positive semidefinite.  Conversely, specialize the universal cone assertion to coefficients
`(0,0,1)`; determinant positivity on that pure prime--archimedean ray is exactly the existing RH
criterion.  Positive determinants also trigger the generic finite-spectral and finite-state-space
exclusion theorems.

## Audit

- **[CORPUS]:** HTGeometry contains only the unconditional black-hole/reciprocal two-ray cone
- **[CORPUS]:** RHTower characterizes RH only on the pure prime--archimedean ray
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; exact three-ray cone equivalence and uniform finite-model exclusions are absent
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — terminal cross-folder cone closure found; paper proof closed
