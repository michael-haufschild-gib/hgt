# Projective-horizon reflection recurrence law

- **ID:** projective-horizon-reflection-recurrence-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus closure of `ProjectiveHorizonCausticReflection` and `ProjectiveHorizonHankelSecant`
- **Statement:** A reflection-fixed coefficient sequence has a nonzero annihilating recurrence on every consecutive Hankel window whose corresponding horizon rectangle has odd area; in particular, on every odd-start, odd-size window.

## Goal

Turn the protected parity zero of a projective-horizon caustic into its missing operational Hankel
recurrence statement.

## Gates

- [x] 0 → 1  in-progress: determinant-parity and Hankel-kernel terminals aligned
- [x] 1 → 2  fully-proven: dependency-closed reindexing proof
- [x] 2 → 3  formalized: `exists_reflectionFixed_shiftedHorizon_windowRecurrence_of_odd_area`
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

## Lean certificate

File: `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonReflectionRecurrenceLaw.lean`
(imported by `GaloisForLFunctions.HTGeometry`).

- `GaloisForLFunctions.HTGeometry.exists_reflectionFixed_shiftedHorizon_windowRecurrence_of_odd_area`
  — for a field `K` of characteristic zero, a reflection-fixed sequence `h` (`(-1)^k h k = h k`)
  and `Odd (m * (s + m - 1))`, there is `c : Fin m → K`, `c ≠ 0`, with
  `∑_j h (s + r + j) * c j = 0` for every `r : Fin m`;
- `..._of_odd_start_size` — the same conclusion from `Odd s` and `Odd m`.

The proof is the paper chain: `rectangularSchurToeplitz_det_eq_zero_of_reflectionFixed` at horizon
index `s + m - 1` (odd area kills the determinant in characteristic zero),
`rectangularSchurToeplitz_reindex_rev_eq_shiftedHorizonHankel` plus `Matrix.det_reindex` (column
reversal changes the determinant only by a unit sign), and
`shiftedHorizonHankel_det_eq_zero_iff_exists_windowRecurrence` (singular Hankel window ⟺ nonzero
annihilating recurrence).

Both theorems use only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-07-22 — independent terminal statements joined; paper proof closed
- 2026-07-26 — verified formalized in the tree, axiom-clean; card moved to `3-formalized`
