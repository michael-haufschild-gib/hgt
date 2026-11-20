# Review-2011 §2.1: work with known mathematics

- **ID:** R2011-KM
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) packages
- **Source:** docs/reports/review-2011/obstacles-summary.md §2.1
- **Statement:** formalize the eight §2.1 packages (5/6 faces, ECS↔PSM identity, Green transfer, pilot baselines, Λ_X pincer, verified height, twin suite, adversary bookkeeping), easiest first.

## Goal
Each package removes an obstacle without a new inequality. Order of work: 5/6 faces → ECS↔PSM identity → Green transfer → Λ_X pincer constant → pilot baselines → twin suite → adversary bookkeeping → verified height.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Packages
| # | Package | Lean module | Status |
|---|---|---|---|
| 1 | 5/6 faces (PSM, ECS, WD, MC, AAD) + unconditional faces at the 20999/24000 strip | SquareRootThreshold/TheFiveSixthsFacesOfTheZeroAbscissa (`fiveSixths_faces`, `fiveSixths_wd_face`, `unconditional_faces`, `unconditional_wd_face`) | formalized |
| 2 | ECS ↔ PSM identity with explicit constants | ExclusionOfTheCriticalState/Wall/TheTerminalJointHeightIsTheSquaredHalvingIncrement (`mul_terminalJointHeight`, `abs_terminalFlank_add_terminalOddHalf_le`: constant 95, `abs_mul_sum_terminalJointHeight_sub_sq_le`) | formalized |
| 3 | Green transfer D ↔ E(H)−E(H/2) | ExclusionOfTheCriticalState/Wall/TheMidpointAndTheHalvingIncrementShareOneSidedExponents (`error_le_of_terminalOddHalf_le`: coefficient 1/(1−2^(−b)), `midpoint_halving_joint_spectra`) | formalized |
| 4 | Pilot baselines (i)–(iii) | (i) ExceptionalLayerTheory/SquareConductors/TheIndependentEndpointPriceOfTheFirstCofactorOctave (`abs_firstCofactorOctave_le`: exponent 1/3+2b/3 for b>Θ; unconditional above 32999/36000; 8/9 under Θ≤5/6) · (ii) SignedArithmeticCorrespondences/TheOddEvenCouplingOfTheWeilCombSeesOnlyThePrimeTwo (`contact_odd_even`, `combSiteRow_of_odd`, `combSiteRow_twoBlock`) · (iii) CountingHolography/Sections/TheGramOfTwoPrimeShellCopiesOfOneWitness (`tendsto_gram_primeShellCopies`, `eventually_negDef_primeShellCopies`, `eventually_not_negDef_primeShellCopies`) | formalized |
| 5 | Λ_X pincer constant | ZeroConfigurationGeometry/HeatScaleRepulsion/TheLocalNewmanPincerCannotSeeTheStrip (`im_eq_zero_of_pairModelHeat_critical_eq_zero`, `pairModel_persistence_misses_pincer_threshold`) | formalized |
| 6 | Verified height beyond 67 | — | not started (stopped by user 2026-11-20) |
| 7 | Twin test suite | ScaleSignedIncidenceCriticality/TheTwinTestSuite (`twin_stepanov_oneOff`, `twin_stepanov_realOneOff`, `twin_comb_liouville`, `twin_eulerSymmetric_floor`, `twin_fixedAperture`, `twin_primeTwo_schur`) | formalized |
| 8 | Adversary bookkeeping | — | not started (stopped by user 2026-11-20) |

## Findings
- WD module `ConjugateDiagonalGeometry/NearLineLogMean/SuperpolynomialMobiusOrder` did not compile against current Mathlib; repaired (5 API fixes) and wired.
- Green transfer: the kernels with symbols (1−2^(−s))/(2·3^s−2^s−4^s) and its reciprocal are signed, so D and ΔE exchange one-sided bounds only through Θ; at the level of exponents the exchange is lossless (both are exact meters).
- Λ_X pincer: excluding depth d needs c·d² > 6600/9991. The pair model (Lindelöf-size, RvM spacing) is real-rooted at its collision heat t* < δ/L, so any persistence constant valid for it has c·δ < 1, hence c·δ² < 1/2 < 6600/9991. At the strip depth the pincer needs c > 4.69, the pair-model ceiling is 24000/8999 ≈ 2.67. Answer: the pincer carries no strip information unless its lower law uses arithmetic absent from the pair model.

- Odd sector: the even–odd block of the Weil comb has contacts only on the rays i = 2^k·m (weight log 2); every odd prime enters the odd-sector Schur complement through the odd block C alone.
- Two copies of one witness at log-distance Δ: limit Gram [[I, A(Δ)], [A(Δ), I]], A = probeAutocorr; negative-definite pair iff |A(Δ)| < |I| (asymptotically).
- Verified height: the height-67 proof is phase-free (Fejér budget, band L = 3). Phase-free bounds peak near L = 3 (left side 2(2 − 4(1−e^{−L/2})/L) grows slower than the worst-case prime polynomial), so going beyond 67 needs phase-dependent (zero-locating or γ-local) certified evaluation.

## Log
- 2026-11-20 — packages 1–5 and 7 formalized and wired; loop stopped by user before 6 and 8.
- 2026-11-20 — created; Θ ≤ 20999/24000 is a Lean theorem (`ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths`), so every face also has an unconditional reading.
