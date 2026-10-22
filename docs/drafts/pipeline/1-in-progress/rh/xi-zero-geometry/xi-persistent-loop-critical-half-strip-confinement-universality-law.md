# Xi persistent-loop critical-half-strip confinement universality law

- **ID:** xi-persistent-loop-critical-half-strip-confinement-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated collision of persistent descended rung-one loop character with
  Euler far-field all-rung loop drain
- **Statement:** A persistently nontrivial descended rung-one Xi loop can never be based right of
  `Re ρ = 1`; if its base lies right of the critical line, it is confined to
  `1/2 < Re ρ ≤ 1`, without assuming in advance that `ρ` is an Xi zero.

## Goal

Extract a spatial law from two opposing local-loop phases. Existing defect theorem uses
persistent nontriviality only after assuming an Xi zero. Existing far-field theorem forces every
sufficiently small loop character to be trivial. Their radius intersection should confine the
loop invariant itself, eliminating the zero hypothesis.

## Gates

- [x] 0 → 1 in-progress: full read of the post-Law-423 deck-charge terminal component
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `PersistentXiDefectLoop`
- `xiDescent_farField_allRungLocalLoopDrain`

## Proof

**[PROVED HERE]** Suppose `PersistentXiDefectLoop ρ` and, toward contradiction,
`1 < Re ρ`. Persistent nontriviality supplies a positive radius `Rₚ` below which every descended
rung-one loop has deck character different from one. The far-field all-rung drain, specialized
to rung one, supplies a positive radius `R𝒻` below which the same loop has deck character one.
Choose `r = min(Rₚ,R𝒻)/2`. Positivity gives `0 < r`, and elementary order gives
`r < Rₚ,R𝒻`. The two conclusions concern the identical squared-descent loop, contradiction.
Thus `Re ρ ≤ 1`. Combining this with right-half membership gives
`1/2 < Re ρ ≤ 1`. No Xi-zero premise is used. ∎

## Strict gain over corpus endpoints

The defect theorem confines only actual odd-order Xi zeros. The new law confines the persistent
loop observable itself, before a zero or analytic order is supplied. This shows Euler
zero-freeness imposes a hard support wall directly on the local monodromy phase.

## Lean formalization

- Upper-wall theorem:
  `persistentXiDefectLoop_re_le_one`
- Critical-half-strip theorem:
  `persistentXiDefectLoop_criticalHalfStripConfinementUniversality`
- Module:
  `GaloisForLFunctions.RHTower.XiPersistentLoopCriticalHalfStripConfinementUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/RHTower/XiPersistentLoopCriticalHalfStripConfinementUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Post-proof arXiv searches found nearby zero-free-half-plane criteria, winding/vorticity pictures
of zeta zeros, and operator-theoretic local-factor models. No result states that persistent
nontrivial dyadic deck character on every sufficiently small squared-descent loop, independently
of a zero premise, forces `Re ρ ≤ 1`. Novelty remains a negative-search conclusion, not a claim
of bibliographic completeness.

## Log

- 2026-07-23 — persistent-loop/far-field terminal component read in full.
- 2026-07-23 — dependency-closed radius-collision proof completed before Lean source or
  literature search.
- 2026-07-23 — exact-file Lean verification passed; module wired into the RHTower umbrella.
- 2026-07-23 — post-proof literature audit found no exact persistent-loop confinement theorem.
