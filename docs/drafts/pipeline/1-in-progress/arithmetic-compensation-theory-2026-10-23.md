# Arithmetic Compensation Theory (arithmetic compatibility and compensated coercivity)

- **ID:** arithmetic-compensation-theory
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (programme)
- **Source:** ../../../reports/review-2210/astra.md
- **Statement:** Develop the programme proposed in the report as its own Lean area
  `formal/GaloisForLFunctions/ArithmeticCompensationTheory/` with umbrella
  `ArithmeticCompensationTheory.lean` and a foundational README.

## Goal

Turn the report's paper deductions into unconditional Lean theorems, build the tools it names
(compensated decompositions, scale transitions with connection terms, defect profiles, graded
estimates), and answer each of its seven research questions by the strongest unconditional
statement available: a positive theorem, an exact equivalence that locates the question on the
zero-width scale, or a sharp obstruction with its positive survivor.

## Gates

- [x] Pillar 1: prime-comb translation law and sharp rate `4e^{2r}` (report (1)-(2)).
- [x] Pillar 2: quantifier corrections — signed vs positive-part budget, core limit (4),
      aperture-loss rate (6), adverse first-cell work.
- [x] Pillar 3: 17/30 short-window transfer into the BVI block theorem (range `30/17`).
- [x] Compensation coordinates (8), the actual PM-Ramanujan instance and its `log⁻⁶P` rate.
- [x] Comb resolvent law, with `J(F) > 0` on every nonzero test.
- [x] Corrector criterion (9)-(10) and its RH dictionary.
- [x] Dyadic summability of the compensation defects; exact price `(k+1)(k+2)/2` of a change of origin.
- [x] README written; umbrella `ArithmeticCompensationTheory.lean` wired into `MainTheorems`;
      area registered in `scripts/formal_tools.py`.

## Lean status

All fourteen modules pass `lake --old env lean` (2026-10-23); no `sorry`/axiom.

Open (README §8): two-scale compensation rate, arithmetic corrector construction, receiver
blow-up profiles, compensated full-ledger remainder, balanced regime, function-field calibration.

## No-go closure

Not applicable yet.

## Log

- 2026-10-23 — created; sources audited (AIP comb reduction, ACCE core debt / aperture
  transport, ACT ceiling, PM-Ramanujan cancellation, BVI block theorem, 17/30 window, SRT graded
  floor and its converse).
