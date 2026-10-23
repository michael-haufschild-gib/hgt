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

- [ ] Pillar 1: prime-comb translation law and sharp rate `4e^{2r}` (report (1)-(2)).
- [ ] Pillar 2: quantifier corrections — signed vs positive-part budget, core limit (4),
      aperture-loss rate (6), adverse first-cell work.
- [ ] Pillar 3: 17/30 short-window transfer into the BVI block theorem (range `30/17`).
- [ ] Compensation coordinates (8) and the actual PM-Ramanujan instance.
- [ ] Comb defect form / resolvent law (profile classification for the raw comb).
- [ ] Corrector criterion (9)-(10).
- [ ] README written; umbrella wired into MainTheorems.

## Module plan (status: written / scratch-checked / audited)

| Module | Content | Status |
|---|---|---|
| ThePrimeCombIsATranslation | `S_r ~ 2e^r`, concentration, `E_r ~ 4e^{2r}`, `L²` translation, charge → 0, odd smooth family | scratch-checked |
| TheCombAtTheHorizonIsAResolvent | depth law, horizon-law averages, `E_r(F)/S_r² → J(F)`, `J > 0` | written |
| CompensationCoordinates | Pythagorean law; PM-Ramanujan instance | scratch-checked |
| TheSignedBudgetIsStrictlyWeakerThanThePositivePart | lacunary countermodel | scratch-checked |
| TheCoreDebtOnAPositiveIntervalIsAZetaLogRatio | limit (4), horizon-free bound | scratch-checked |
| TheApertureFloorMustDecayDoublyExponentially | (6), no transported floor, harmonic failure | scratch-checked |
| TheFirstCellCarriesAdverseWork | `W_1(ε) → −1/2` | scratch-checked |
| TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange | uniform window, BVI at 17/30, range 30/17 | scratch-checked (main theorem body is a copy of BVI's) |
| TheAdaptedEnergyIsExactlyAdmission | corrector criterion and RH dictionary | written |

Scratch-checked = compiled against Mathlib with stubbed corpus inputs (corpus oleans were being
rebuilt by other agents). Final audit = `lake --old env lean` on each file.

## No-go closure

Not applicable yet.

## Log

- 2026-10-23 — created; sources audited (AIP comb reduction, ACCE core debt / aperture
  transport, ACT ceiling, PM-Ramanujan cancellation, BVI block theorem, 17/30 window, SRT graded
  floor and its converse).
