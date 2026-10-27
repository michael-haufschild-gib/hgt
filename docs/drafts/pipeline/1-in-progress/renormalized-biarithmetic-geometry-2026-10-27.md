# Renormalized Biarithmetic Geometry programme

- **ID:** rbg
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/astra.md, Question 3
- **Statement:** Develop RBG: survival of positivity through renormalization, counterterm rank of
  the two places, dyadic amplification of the Hecke defect, gauge fixing by log-cells, gauge charge
  of couplings, critical discs vs terminal cones, chirality law.

## Goal
Lean folder `formal/GaloisForLFunctions/RenormalizedBiarithmeticGeometry/`, umbrella
`RenormalizedBiarithmeticGeometry.lean`, foundational README. Answer the seven questions of astra §3.2
by theorems or sharp no-gos with survivors.

Territory: AES (ArithmeticElectrostatics, other agent) owns torsion self-intersections and counterterm
rates; RBG owns the abstract survival law and the rank comparison, imports AET/BGG/CDG/ACP.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs for each pillar
- [ ] 2 → 3  each pillar in Lean, audited with `lake --old env lean`

## Pillars and modules

| Pillar | Module |
|---|---|
| R1 survival law (Finsler–Debreu), scalar counterterm vacuity | `TheRenormalizationSurvivalLaw` |
| R2 lattice germ → digamma; CPD on `Σc = 0` | `TheArchimedeanGermSurvivesOnItsPolarHyperplane` |
| R3 torsion counterterm full rank; renormalized limit indefinite on `{1, p}` | `TheCountertermRankDichotomy` |
| R4 dyadic amplification, fixed loss `D`, RH ⇔ sub-doubly-exp dyadic growth | `TheDyadicAmplificationOfTheHeckeDefect` |
| R5 cell dilation BS(1,m), covariant only at Euler gauge | `LogCellsFixTheGauge` |
| R6 gauge charge: blind ⇔ `nab` square | `TheGaugeChargeOfACoupling` |
| R7 pair sign law, critical discs ↔ terminal cones | `CriticalDiscsAndTerminalCones` |
| R8 chirality: positive deformations have trivial units | `ChiralityIsTheTrivialityOfUnits` |

## Log
- 2026-10-27 — created; README first draft written.
