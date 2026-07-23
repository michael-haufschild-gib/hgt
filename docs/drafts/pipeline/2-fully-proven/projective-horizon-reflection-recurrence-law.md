# Projective-horizon reflection recurrence law

- **ID:** projective-horizon-reflection-recurrence-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** whole-corpus closure of `ProjectiveHorizonCausticReflection` and `ProjectiveHorizonHankelSecant`
- **Statement:** A reflection-fixed coefficient sequence has a nonzero annihilating recurrence on every consecutive Hankel window whose corresponding horizon rectangle has odd area; in particular, on every odd-start, odd-size window.

## Goal

Turn the protected parity zero of a projective-horizon caustic into its missing operational Hankel
recurrence statement.

## Gates

- [x] 0 → 1  in-progress: determinant-parity and Hankel-kernel terminals aligned
- [x] 1 → 2  fully-proven: dependency-closed reindexing proof
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

Apply the reflection-fixed odd-area theorem to the rectangular Schur--Toeplitz section with horizon
index `s + m - 1`.  Canonical column reversal identifies that section with the shifted Hankel
matrix.  Determinant under reindexing differs only by a permutation sign, so zero transfers to the
Hankel window.  The existing determinant-kernel equivalence then produces a nonzero coefficient
vector annihilating every row of the visible window.  Odd `s` and odd `m` imply the required area
parity.

## Audit

- **[CORPUS]:** reflection module stops at determinant vanishing
- **[CORPUS]:** Hankel-secant module characterizes determinant vanishing by a recurrence but does not consume reflection parity
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; forced recurrence and odd-start/odd-size form are absent
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — independent terminal statements joined; paper proof closed
