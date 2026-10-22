# Xi-defect persistent local-loop universality law

- **ID:** xi-defect-persistent-local-loop-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Positive-survivor closure of the failed quadrant--seam route, all-rung
  Xi-descent local-loop charge transport, and the open critical-strip zero theorem
- **Statement:** A right-half Xi defect is exactly an open-critical-strip Xi zero whose rung-one
  deck character is nontrivial on every sufficiently small descended circle; this persistent
  loop detector is simultaneously equivalent to odd local analytic order.

## Goal

Extract the strongest positive local theorem left by the refuted quadrant--seam terminal
dichotomy: replace unsupported global charge transport with an exact, radius-stable local detector
of the defect object already defined by that failed route.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: tree source and exact `lake env lean` passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `XiDefect`
- `xiDefect_charge_iff_odd`
- `deckChar_loopCharge_xiDescent_center_sq`
- `carrierCharge_xiDescent_center_sq_allRungs`
- `xi_zero_re_mem_open_unit`

## Proof

`[PROVED HERE]` At every right-half point the all-rung small-loop theorem supplies a positive radius
on which the deck character of every descended circle equals Xi's local carrier charge.  At rung
one, a defect's nontrivial point charge therefore makes every sufficiently small loop character
nontrivial.

Conversely, intersect the radius witnessing persistent nontriviality with the radius supplied by
the local-loop equality and choose half their minimum.  The loop character at that radius is both
nontrivial and equal to Xi's point charge, so the point charge is nontrivial and the right-half zero
is a defect.  The existing charge parity theorem identifies this with odd analytic order.  The
global Xi zero-free theorem confines every zero to `0 < Re ρ < 1`; right-half membership sharpens
the defect location to `1/2 < Re ρ < 1`.

No numerical computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiDefectPersistentLocalLoopUniversalityLaw`
- Main theorem:
  `RHTower.xiDefect_persistentLoop_openStrip_oddOrderUniversality`
- Reusable connector:
  `RHTower.xiDefect_iff_rightHalfZero_persistentLoop`
- New invariant:
  `RHTower.PersistentXiDefectLoop`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/XiDefectPersistentLocalLoopUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Final axiom audit and module build deferred to final audit.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- R. R. Hall, *On the Zeros of the Riemann Zeta-Function*
  ([DOI](https://doi.org/10.1112/S0024610798006942)), studies multiplicity bounds and distinct
  zeros in short intervals, not a square-descended persistent local deck-character
  characterization of odd Xi zeros.
- David Farmer and Steven Gonek, *Pair correlation of the zeros of the derivative of the Riemann
  ξ-function* ([arXiv:0803.0425](https://arxiv.org/abs/0803.0425)), studies zero statistics and
  simplicity consequences under RH, not local loop/deck detection of an individual off-line
  odd-order zero.
- Cabiria Andreian Cazacu and Dorin Ghisa, *Fundamental Domains of Gamma and Zeta Functions*
  ([arXiv:0911.5138](https://arxiv.org/abs/0911.5138)), discusses branched-cover geometry and
  covering transformations for zeta, but the located statement does not give this exact
  Xi-square-descent, every-small-radius, rung-one character equivalence.

Targeted searches for Xi square descent, local winding, multiplicity, and deck transformations
found standard argument-principle and zero-multiplicity ingredients, but no theorem identifying
the corpus's right-half `XiDefect` simultaneously with open-strip location, persistent
nontriviality of every sufficiently small descended dyadic loop character, and odd analytic
order.  Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — Whole-corpus semantic pass revisited the failed quadrant--seam card against later
  Xi-descent local-loop theorems.
- 2026-07-23 — Radius intersection proved the converse point-charge reconstruction; exact Lean
  source passed and umbrella import added.
- 2026-07-23 — Post-proof literature audit found neighboring multiplicity and branched-cover
  work, not the exact positive-survivor law.
