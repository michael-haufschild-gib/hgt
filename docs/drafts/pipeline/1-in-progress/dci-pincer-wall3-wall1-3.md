# Dilution–Crystallization–Incommensurability (DCI) Pincer Across Wall 3 and Wall 1.3

- **ID:** dci-pincer-wall3-wall1-3
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2110/argon.md · §1.2 Mechanism 1
- **Statement:** Unconditional formalization of the Dilution–Crystallization–Incommensurability (DCI) Pincer in `GaloisForLFunctions.DilutionCrystallizationPincer`: (1) multi-pair diluted periodic patterns and crystals in an on-line background `L` become visible at logarithmic aperture `a ≍ (1/2δ) log(L/ℓ)` (`DilutedPatternAndCrystalVisibilityLaw`), (2) above the archimedean height horizon `T` where `log(1 + T/8)` dominates the diluted visibility aperture `a`, `ζ` satisfies unconditional single-height Weil positivity while any diluted off-line lattice of depth `δ` violates the level-`a` Hodge index (`ArchimedeanDominationOfDilutedVisibility`), (3) crystalline off-line configurations have difference-test Weil form supported purely on the harmonic lattice `nL` and vanishing in all gaps `|v - nL| > 2w`, whereas `ζ`'s prime polynomial on the Kronecker–Bohr prime torus has strictly positive aligned supremum forcing either sub-horizon Weil negativity or exponential height escape (`PrimeTorusCrystallineResonanceObstruction`), and (4) any sub-exponential growth bound on unit-window off-line depth mass along the ground-state support forces `polarGroundEnergyRate = zetaZeroWidth` (`MasterDCIPincerTheorem`).

## Goal
To work through §1.2 Mechanism 1 of Project Argon (`docs/reports/review-2110/argon.md`), coupling the four previously isolated legs of the `SquareRootThreshold` and `RHTower` programmes into an unconditional, dependency-closed Lean 4 theorem suite inside its own subfolder `formal/GaloisForLFunctions/DilutionCrystallizationPincer/`, and to isolate the exact remaining local-clustering pinch where Wall 3 and Wall 1.3 meet.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions.DilutionCrystallizationPincer`, audited with `lake env lean --old`
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
1. **Leg 1 (`DilutedPatternAndCrystalVisibilityLaw.lean`):** Define `dilutedPatternConfig` and `dilutedCrystalConfig` (a `P`-pair periodic off-line pattern/crystal of period `2π/ℓ` superposed on a dense on-line lattice of spacing `2π/L`). Prove the exact difference-test Weil form decomposition `W_dilutedPatternConfig_lag_eq` and `W_dilutedCrystalConfig_lag_eq`, prove that the `P`-pair crystal vanishes on modes `1 ≤ m < P` and has effective diluted spacing `Pℓ`, and prove the logarithmic visibility threshold where the off-line crystal or non-crystalline pattern defeats the on-line background `2L`.
2. **Leg 2 (`ArchimedeanDominationOfDilutedVisibility.lean`):** Couple `ZetaSingleHeightPositivityAboveArchimedeanHorizon` (`zetaZeroConfig_re_W_heightShift_ge`) with `DilutedOffLineLatticeHidingLaw` (`dilutedLattice_not_hodgeIndex_of_lt`) to prove the unconditional **Sub-Barrier DCI Comparison Theorem**: at any height `ξ` where the archimedean digamma main term dominates the diluted visibility aperture `a`, `ζ`'s height-shifted localized Weil form is strictly positive on the very witness `f` that makes the diluted off-line lattice strictly negative.
3. **Leg 3 (`PrimeTorusCrystallineResonanceObstruction.lean`):** Couple `LagFamilyMeetsTheCrystalAtTheThreshold` (`W_offLineLattice_lag_nat_mul`, `W_offLineLattice_lag_eq_of_gap`) with `KroneckerBohrPrimePhaseRealizationAndExponentialHeightEscape` (`exists_height_re_W_zeta_le_of_primeWindow`, `zeta_kronecker_weil_negativity_or_exponential_height_escape`) and `ZetaLocalizedFormWindowedVarianceLaw` to prove the **Crystal-vs-Prime-Torus Incompatibility Law**: a uniform crystal's lag response is supported purely on `{nL}` and zero in every gap `(nL + 2w, (n+1)L - 2w)`, whereas `ζ` carries an irreducible positive prime-torus amplitude `primeWindowAlignedAmplitude w v > 0` at every prime-Containing window.
4. **Leg 4 (`MasterDCIPincerTheorem.lean`):** Prove a strengthened criterion for `polarGroundEnergyRate = zetaZeroWidth` (showing how local off-line depth control or dilution closes the ground-energy rate gap) and assemble the 4-leg unconditional **Master DCI Pincer Theorem** (`dci_pincer_master_theorem`).

## Log
- 2026-10-22 — Created in `1-in-progress` and began Lean 4 formalization in `formal/GaloisForLFunctions/DilutionCrystallizationPincer/`.
