# Selective Multiscale Arithmetic Positivity (SMAP) programme

- **ID:** smap
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2810/obstacles-summary.md §2.5; Q1–Q3
- **Statement:** Develop selective (twin-separating) positivity for the Weil form on complete, self-similar arithmetic sources.

## Goal
Pillar theorems in `formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/`:
1. Selectivity necessity / selection at every root (twin-blind atomic positivity impossible).
2. Pole-hyperplane identity for atomic tests (discrete Σx/√n ↔ continuous ∫f e^{-u/2}).
3. Selective positivity window: ζ ≥ 0, Liouville < 0 on pole-hyperplane atomic tests beyond Robin–Euler.
4. Dyadic multiresolution decomposition + level-Toeplitz law.
5. RG index law (Haynsworth) + block-dominance criterion.
6. Prime-2 bottleneck (p log p/(p−1) increasing).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs per pillar
- [ ] 2 → 3  Lean modules audited with `lake --old env lean` (13 modules, each checked clean when written; final audit pending)

## Approach
Reuse: SSHA atomic families (`atomicTest`, every-root theorems), ALG `ThePoleDefectPaysThePole`
(`eventually_markovEnergy_ge_defect`), RAPT pole gap (`ThePrimeFormHasASpectralGapBelowItsPole`),
RAPT Liouville separation, ACS `HaarCellCoarseSplitting`, SAHT translation invariance.

## Log
- 2026-10-28 — created; README first draft written.
- 2026-10-28 — Lean (checked, clean): PositivityAtEveryRootSelectsTheVonMangoldtWeight (selection at every root,
  twin-blind impossibility); ThePoleHyperplaneIsTheHarmonicHyperplane (pole moments = harmonic sums; twins differ
  only in prime form); ThePoleHyperplaneSeparatesTheFullWeilForms (gap-paid ζ bound; Liouville below ζ by uniform
  margin; ζ not minimum of gauge orbit on hyperplane); TheConductorTwoIsTheFirstExcitation (E_m − E_1 ≥ 2log2,
  equality iff m=2; hyperplane prime gap ≤ 2log2). Next: RG/Schur calculus; dyadic multiresolution + level-Toeplitz.
- 2026-10-28 — Lean (checked, clean): ALevelIsPaidByItsReserve (level payment, rg_step, rgMargin recursion,
  Schur transparency, block dominance); TheCompleteSourceIsADyadicMultiresolution (doubled cell, RG step,
  multiresolution, level-Toeplitz); TheHyperplaneGapIsTheSelectiveMargin (ζ gap ∈ (0,2log2], Liouville none);
  TheHaarFloorIsTwinBlind (high-detail floor for every |ω|≤1 with same index). Umbrella + MainTheorems wired.
  README foundational version written. Open: coarse selective transfer, cross-level coupling costs,
  generator-orbit symbols, sharp gap lower bound, virial upper bound.
- 2026-10-28 — Lean (checked, clean): TheSelectiveGardingInequality (pole projection; D_N ≥ G·off-pole mass for
  all x; Gårding on every narrow atomic test); ThePoleHyperplaneIsRenormalizationInvariant (dyadic shift =
  T_{log 2}; hyperplane invariant; two-level hyperplane tests gap-paid); ThePoleCouplesTheLevelsHyperbolically
  (cosh law; rank-two hyperbolic pole on level orbits; dyadic harmonic hyperplane);
  SeparatedLevelsCoupleThroughTheChebyshevError (Gamma coupling ≤ π e^{−4δ}·mass, 4^{−(k−j−1)} dyadic; coupling =
  centered Chebyshev / prime comb on hyperplane); TheSelectiveMarginIsTwoLogTwo (ζ gap exactly 2log2 via RAPT
  sharp Poincaré; sign gauges gap 0, Liouville exactly 0; sharp Poincaré/Gårding). Correction: the dyadic
  generator orbit is not a one-prime problem (width-w copies read the Chebyshev increment near 2^m).
  Open: signed Chebyshev costs between levels; touching levels; orbit Toeplitz symbol; coarse transfer;
  margin extremality among twists; virial upper law.
