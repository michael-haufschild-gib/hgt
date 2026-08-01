# Function-field spectral-closure universality law

- **ID:** function-field-spectral-closure-universality-law
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** cross-folder closure of `FunctionFieldFE` and `MultisetSymmetricDetermination`
- **Statement:** A finite Frobenius multiset is closed under `ω ↦ q/ω` if and only if its elementary symmetric coefficients satisfy the complete `q`-weighted reciprocal functional equation; coefficients only through the multiset cardinality already suffice.

## Goal

Determine whether the coefficient-level function-field functional equation merely follows from a
chosen spectral pairing or intrinsically determines that pairing.

## Gates

- [x] 0 → 1  in-progress: exact Lean statements aligned and prior corpus searched
- [x] 1 → 2  fully-proven: dependency-closed proof passed exact Lean check
- [x] 2 → 3  formalized: exact Lean theorem, direct elaboration, final module build, lint, and axiom audit pass
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

The forward implication is the existing `functionField_esymm_FE`.  For the converse, scale the
inverse multiset by `q`; homogeneity identifies each of its elementary symmetric functions with
the weighted reciprocal coefficient.  The assumed coefficient identities therefore make all
elementary symmetric functions agree with those of the original multiset.  Equal cardinality is
automatic under `Multiset.map`, and `multiset_eq_of_esymm_eq` recovers equality of multisets.

## Audit

- **[CORPUS]:** `FunctionFieldFE` proves only spectral closure → coefficient and polynomial FE
- **[CORPUS]:** `MultisetSymmetricDetermination` proves abstract recovery from symmetric data
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; no existing theorem supplies the converse or the bounded coefficient completeness statement
- **Status:** `[PAPER-PROVED] [EXACT-LEAN-PASS] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — terminal cross-folder closure found from exact Lean statements
- 2026-07-22 — exact development check passed with `lake env lean GaloisForLFunctions/RHTower/FunctionFieldSpectralClosureUniversalityLaw.lean`
