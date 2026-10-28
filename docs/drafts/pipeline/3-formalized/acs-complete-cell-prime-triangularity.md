# Complete pair averages have no outgoing balanced prime component

- **ID:** acs-complete-cell-prime-triangularity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [complete-cell mixed payment](../1-in-progress/acs-complete-cell-mixed-payment.md)
- **Statement:** Every complete cell pair splits exactly into its weighted average and balanced detail; the real average-to-detail pairing vanishes under every integer prime translation.

## Goal

Keep both independent coefficients on every adjacent pair while identifying the exact mixed prime term that remains to be paid. No average direction is deleted.

## Exact result

Write `E_a=cellAtom(2a)`, `O_a=cellAtom(2a+1)`, `C_a=E_a+O_a`, and let `H_a=haarAtom a`. For `a≥1`,

`u E_a + v O_a = (haarRightCoeff(a)*u + haarLeftCoeff(a)*v) C_a + (u-v) H_a`.

`coarseAtom_eq_shift` identifies `C_a` with the actual half-line shift of `cellAtom a` by `log 2`.

For every `m≥2`, arbitrary finite horizons, and arbitrary signed real coefficients,

`Re ⟪T_(log m) (coarseSection c X), haarSection d Y⟫ = 0`.

The exact endpoint formula underlying this is

`Re ⟪T_(log m) cellAtom a, H_b⟫ = haarMass(b) * (1_((a+1)m=2b+1) - 1_(am=2b+1))`.

## Gates

- [x] Both original cell coefficients retained by an exact Hilbert-vector identity.
- [x] Actual translated cell pairings used, with every successor cell present.
- [x] Entire finite average-to-detail block proved zero.
- [x] Direct stage-3 promotion after exact Lean verification; no stage-2 parking.
- [x] Five transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

## Matched proof

The two Haar coefficients sum to one and pay the same mass on their respective cells, giving the exact source splitting. Integer translation subdivides each complete cell. Pairing with a balanced detail detects only translated endpoint jumps. The shared interior endpoints cancel between the two cells of a coarse pair; its outer endpoints are even and cannot hit the odd midpoint of a balanced pair. Finite signed sums preserve this zero pairing.

## Lean evidence

[HaarCellCoarseSplitting.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellCoarseSplitting.lean): `cellPair_eq_average_add_detail`, `coarseAtom_eq_shift`, `inner_shift_cellAtom_haarAtom`, `inner_shift_coarseAtom_haarAtom`, `inner_shift_coarseSection_haarSection`.

The exact file passed `lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellCoarseSplitting.lean`, without warnings. Log: `/tmp/acs-haar-coarse-final.log`. The ACS umbrella import is wired; the umbrella was not compiled.

## Remaining parent obligation

The detail-to-average prime orientation is not zeroed or discarded. Its signed interaction, the Gamma coupling, and both original poles still require full mixed Weil payment.

## Log

- 2026-10-28 — Exact vector splitting and all five transitive axiom audits passed; promoted directly to stage 3.
