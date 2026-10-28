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
- [x] Lean audit: all 16 modules checked clean with `lake --old env lean`; headline theorems use only propext, Classical.choice, Quot.sound

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
- 2026-10-28 — Lean (checked, clean): TheSelectiveMarginIsTwoLogTwo extended (every hyperplane meets the top
  eigen-plane; ζ has the largest margin among sign gauges ω²=1; zero weight has every gap);
  AMarginNeedsHarmonicCorrelation (S_N(ω)² = o(log N) ⇒ margin 0; positive margin ⇒ S_N² ≥ c log N i.o.);
  FullCorrelationKeepsTheMargin (pole polarization; misalignment cost; S_N/H_N → 1 ⇒ margin 2log2; finite
  flips keep it). Open: margin at intermediate correlation ρ ∈ (0,1).
- 2026-10-28 — Lean (checked, clean): TouchingLevelsCoupleUniformly (translation invariance of the real pairing;
  adjacent levels couple through one constant for every level). AMarginNeedsHarmonicCorrelation and
  FullCorrelationKeepsTheMargin restructured into small lemmas plus pure arithmetic steps (check time 9+ min → ~3 min).
  Final audit of all modules done.
