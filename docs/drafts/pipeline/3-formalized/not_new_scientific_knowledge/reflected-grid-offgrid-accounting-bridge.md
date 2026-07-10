# Reflected Grid Offgrid Accounting Bridge

- **ID:** r7-reflected-grid-offgrid-accounting-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** R7 AFE/reflected-block route; `docs/drafts/rh-monodromy-weight-mismatch/104-checkpoint-deadends-and-open-routes.md`
- **Statement:** For `N ≥ 1`, the canonical completed reflected-grid charge plus any `LedgerFluxPaired` off-grid integer event list is even, hence deck-trivial at level two; any future charge proved equal to that accounted expression is deck-trivial.

## Goal

Type the remaining R7 physical-carrier burden without hiding it: after the canonical completed collision charge is formalized, the only extra parity input needed from off-grid/noncollision events is a `LedgerFluxPaired` certificate plus an equality identifying the physical charge with the accounted grid-plus-offgrid expression.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `reflectedGridOffgridCharge_deckRed_two_eq_one_of_accounted`, `lake build` green, axiom check PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Use `reflectedGridCompletedCharge_even_of_ratio_center_of_one_le` for the completed collision carrier, `ledgerFluxPaired_two_dvd_sum` for the off-grid integer event ledger, and `deckRed_two_eq_one_iff` for the level-two deck statement.

## Log

- 2026-07-06 — formalized in `RHTower/ReflectedGridOffgridBridge.lean`; verified with file build, umbrella build, `/tmp` axiom checks, generated index, and `scripts/formal_tools.py lint --check-generated`.
