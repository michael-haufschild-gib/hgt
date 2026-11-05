# Arithmetic production at square-root precision (APR)

- **ID:** apr-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0511/obstacles-summary.md §2.7.2
- **Statement:** what unconditional statements can produce parity and square-root precision; exact production limit of each classical tool.

## Goal
Build `formal/GaloisForLFunctions/ArithmeticProduction/` with umbrella and README. Answer the four questions of §2.7.2 and the mechanism question.

## Gates
- [x] 0 → 1  README first draft
- [ ] modules below proved, checked, wired
- [ ] README rewritten on established results

## Module plan
1. BilinearFormsAreParityBlind — twist invariance, block-diagonal on prime support.
2. TypeIInformationIsParityBlind — `Σ λ W = Σ c_d λ(d) L(x/d)`, L¹ barrier.
3. MeanValuesBelowTheWindowAreBlind — MVT twist invariance; prime polynomial of Λ and λΛ.
4. TheLinearMollifierIsTheChebyshevError — coefficient identity, sawtooth identity, Cramér inside the defect, sharp mollifier.
5. TheMollifierFloor — floor without pole cancellation, Blaschke form.
6. TheSecondMomentIsALaplaceTransform; TheBandLimitOfTheMollifiedZetaFunction; TheFloorsOfTheMollifiedSecondMoment; TheNecessaryLengthOfAMollifier.
7. LongMollifiersImplyCriticalClustering — named implication.
8. ImpureEulerFactors — exact count, upper bounds, failed count, log-mean, D_win.
9. SelfImprovementOnShiftedProducts — width formula, class law.
10. TheFaithfulUnconditionalInputs — Mertens constant passes three criteria, fails the stabilizer.
11. TheSelbergIntegralDictionary; length–precision law.

## Log
- 2026-11-05 — created; README first draft.
