# Finite Satake reality–Torelli universality law

- **ID:** finite-satake-reality-torelli-universality-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** cross-folder closure of `SatakeReality` and `PowerSumTorelli`
- **Statement:** An `n`-point complex Satake spectrum is conjugation-closed if and only if its secular power sums through order `n` are real; failure is witnessed by one nonreal moment of order at most `n`.

## Goal

Determine whether reality of finite secular data is only a consequence of self-duality or a
complete finite certificate for unlabelled spectral self-duality.

## Gates

- [x] 0 → 1  in-progress: exact Lean statements aligned and prior corpus searched
- [x] 1 → 2  fully-proven: dependency-closed proof passed exact Lean check
- [ ] 2 → 3  formalized: exact Lean theorem and final formal gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

Conjugation closure implies reality of every power sum by `selfDual_moment_real`.  Conversely,
compare the spectrum with its pointwise conjugate.  Reality makes their power sums agree through
order `n`; sharp finite `powerSum_torelli_finite` then identifies the two value multisets.  Negating
the equivalence yields a bounded-order nonreal witness.

## Audit

- **[CORPUS]:** `SatakeReality` proves only conjugation closure → all moments real
- **[CORPUS]:** `PowerSumTorelli` proves sharp reconstruction from the first `n` moments
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; no existing theorem identifies finite Satake self-duality with the sharp finite reality packet
- **Status:** `[PAPER-PROVED] [EXACT-LEAN-PASS] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — terminal cross-folder closure found from exact Lean statements
- 2026-07-22 — exact development check passed with `lake env lean GaloisForLFunctions/RHTower/FiniteSatakeRealityTorelliUniversalityLaw.lean`
