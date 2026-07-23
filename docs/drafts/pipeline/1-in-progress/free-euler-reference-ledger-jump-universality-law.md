# Free Euler-reference ledger-jump universality law

- **ID:** free-euler-reference-ledger-jump-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of the multiplicity ledger jump and finite-Euler
  reference-frame deck cancellation
- **Statement:** Dressing both chart roots before and after a zero crossing by any finite-Euler
  global root preserves the exact multiplicity jump factor `exp(2πi m/n)` for every root level,
  reference depth, and finite reference packet.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit pending

## Corpus inputs

- `deckClass_jump`
- `relative_deckClass_eq`
- `eulerRoot_ne_zero`

## Proof

`[PROVED HERE]` The ledger theorem says that adjoining one enclosed zero of multiplicity `m`
multiplies the bare chart-root deck class by `exp(2πi m/n)`.  A finite-Euler reference root is one
global nonvanishing function.  Multiplying both charts by it cancels identically in each deck
ratio, both before and after the crossing.  Replacing both bare deck classes in the jump equation
by their reference-dressed equals proves the same exact jump.  No computation is used.

## Strict gain over corpus endpoints

The ledger theorem has no reference frame.  The relative-torsor theorem proves pointwise
deck-class invisibility but never transports a deformation jump.  Their closure proves that the
entire charge-flux update rule—not only one static charge—is invariant under every finite-Euler
reference dressing.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.FreeEulerReferenceLedgerJumpUniversalityLaw`
- Main theorem:
  `freeEulerReference_deckClass_jump`
- Source:
  `formal/GaloisForLFunctions/RHTower/FreeEulerReferenceLedgerJumpUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/FreeEulerReferenceLedgerJumpUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the paper proof.  Post-proof audit begins only after exact
Lean verification.

## Log

- 2026-07-23 — Fresh terminal-pair scan exposed the static-reference versus dynamic-ledger seam.
- 2026-07-23 — Dependency-closed proof completed from existing Lean endpoints.
- 2026-07-23 — Exact theorem formalized, checked warning-free, and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof web search attempted; search service returned invalid-response errors, so
  collision audit remains open.
