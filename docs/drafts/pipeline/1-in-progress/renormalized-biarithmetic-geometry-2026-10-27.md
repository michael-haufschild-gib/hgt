# Renormalized Biarithmetic Geometry programme

- **ID:** rbg
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/astra.md, Question 3
- **Statement:** Develop RBG: survival of positivity through renormalization, counterterm rank of
  the two places, dyadic amplification of the Hecke defect and the Hecke moment problem, gauge
  charge of couplings and gauge fixing by log-cells, critical discs and the terminal lens,
  irreversibility of positive deformations, dilution of collective packets.

## Goal
Lean folder `formal/GaloisForLFunctions/RenormalizedBiarithmeticGeometry/`, umbrella
`RenormalizedBiarithmeticGeometry.lean`, foundational README. Answer the seven questions of astra §3.2
by theorems or sharp no-gos with survivors.

Territory: AES (ArithmeticElectrostatics) owns torsion self-intersections and counterterm rates;
RBG owns the survival law and the rank comparison; imports AET/BGG/CDG/ACP/MPG/HTGeometry.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proofs for each pillar below
- [x] 2 → 3  each pillar below in Lean, audited with `lake --old env lean`
- [ ] frontier (README §9): twisted Lerch entries of the twins, one-scale arithmetic bounds,
  terminal ceiling, `λ`-correlation along `a ↦ 2a + 1`, mixed-sign clouds, escape modules

## Pillars (all in Lean)

| Pillar | Module | Key theorem |
|---|---|---|
| survival law, scheme independence, Finsler–Debreu | `TheRenormalizationSurvivalLaw` | `quad_nonneg_on_survivalCone_iff`, `survivalCone_eq_of_regularized` |
| archimedean germ → digamma, CPD on `Σc = 0` | `TheArchimedeanGermSurvivesOnItsPolarHyperplane` | `neg_digamma_hankel_nonneg` |
| torsion counterterm full rank, indefinite limit | `TheCountertermRankDichotomy` | `counterterm_rank_dichotomy` |
| pole-node completion | `ThePoleNodeCompletesTheArchimedeanGerm` | `harmonicKernel_nonneg` |
| periodic germs: survival cone = relations; Ramanujan twins | `TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations` | `periodicGerm_survivalCone_eq`, `ramanujanTwin_survival` |
| Ramanujan orthogonality, exact twin law | `TheRamanujanTwinsSurviveExactlyOnPerOrderRelations` | `ramanujanTwin_survivalCone_eq` |
| twins carry `−φ(m)Λ(t)` in the pole-node block | `TheRamanujanTwinsCarryThePrimes` | `ramanujanTwin_carries_primes` |
| dyadic amplification, RH ⇔ growth rate | `TheDyadicAmplificationOfTheHeckeDefect` | `riemannHypothesis_iff_dyadic_subexp` |
| Hecke moment problem, shell rigidity | `TheHeckeMomentProblem` | `ncard_seenLevels_lt_of_hankel_null` |
| integer-prefix lossless transfer | `IntegerThetaPrefixesReadTheDefectWithoutLoss` | `heckeDefect_le_of_readings` |
| gauge charge = square class, Liouville blindness | `TheGaugeChargeOfACoupling` | `realSignBlind_iff_isSquare`, `sourceForm_nonneg_twist_iff` |
| cells fix the gauge, finite horizons | `LogCellsFixTheGauge` | `cellDilate_two_covariant_iff`, `cellDilate_two_covariant_on_horizon_iff` |
| cell-holonomy defect, Liouville sandwich | `TheCellHolonomyDefectCountsChargedCells` | `hsDefect_liouville_sandwich` |
| critical discs, terminal lens | `CriticalDiscsAndTheTerminalLens` | `xi_ne_zero_of_mem_terminalLens` |
| Harnack on the Carathéodory region, floor spreading | `HarnackOnTheCaratheodoryRegion` | `exists_terminal_floor_spreads` |
| irreversibility | `PositivityIsIrreversible` | `not_positiveDeformation_of_ne` |
| Kronecker dilution, height law, harmonic concentration | `CollectivePacketsDiluteOverIndependentOrdinates` | `sum_abs_le_of_packet_nonneg`, `sum_le_height_mul_of_generated_packet` |
| selectivity battery | `TheSelectivityBatteryOfRenormalizedBiarithmeticGeometry` | `config_dyadic_ge`, `liouville_not_cell_covariant` |
| capstone | `TheLawsOfRenormalizedBiarithmeticGeometry` | `renormalized_biarithmetic_geometry_laws` |

## No-go closure
- **Torsion germ:** no renormalization keeps positivity (survival cone `{0}`, limit indefinite).
  Survivor: archimedean survival on the polar hyperplane and pole-node completion.
- **Square-class criteria:** cannot separate `Λ` from `λΛ`. Survivor: cells fix the gauge.
- **Collective packets over independent ordinates:** buy at most the pole share. Survivor: harmonic
  concentration.

## Log
- 2026-10-27 — created; pillars formalized.
