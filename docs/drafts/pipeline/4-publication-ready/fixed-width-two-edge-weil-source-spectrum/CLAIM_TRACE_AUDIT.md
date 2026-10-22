# Claim trace audit

Paper: `A Local-to-Global Dichotomy for the Riemann Hypothesis`

Audit date: 2026-07-27

Status: strengthened divisor-tomography surface passes targeted Lean; final axiom, lint, build, and
referee audits pending.

## Scope rule

Every mathematical headline in `main.tex` must terminate in an unconditional Lean declaration.
Classical contextual statements are cited. Novelty and journal-significance judgments are not
represented as formal theorems.

## Headline trace

| Paper claim | Lean declaration | Module |
|---|---|---|
| Full observable L-series has cutoff-free continuation | `LSeries_xiRectangularWeilLogCoefficient_eq_fullContinuation` | `CCMRectangularFullObservableDivisorTomography.lean` |
| Full observable simple poles are exactly shifted right Xi zeros | `meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one_iff` | `CCMRectangularFullObservableDivisorTomography.lean` |
| Full observable residue is `2 × multiplicity × window weight` | `meromorphicTrailingCoeffAt_xiRectangularWeilFullContinuation` | `CCMRectangularFullObservableDivisorTomography.lean` |
| Normalized full-observable residue recovers analytic multiplicity | `normalizedFullObservableResidue_eq_xiRightMultiplicity` | `CCMRectangularFullObservableDivisorTomography.lean` |
| RH iff full-observable continuation is analytic on `Re s > 1` | `riemannHypothesis_iff_fullObservableContinuation_analytic_rightOne` | `CCMRectangularFullObservableDivisorTomography.lean` |
| Complexified prime--Gamma source tail equals observable tail | `xiRectangularPrimeGammaTailDirichletCoefficient_eq_weil` | `CCMPrimeGammaSourceDivisorTomography.lean` |
| Prime--Gamma source L-series equals its continuation initially | `LSeries_xiRectangularPrimeGammaTailDirichletCoefficient_eq_continuation` | `CCMPrimeGammaSourceDivisorTomography.lean` |
| Prime--Gamma source poles are exactly shifted right Xi zeros | `meromorphicOrderAt_xiRectangularPrimeGammaTailContinuation_eq_neg_one_iff` | `CCMPrimeGammaSourceDivisorTomography.lean` |
| Normalized prime--Gamma source residue recovers multiplicity | `normalizedPrimeGammaTailResidue_eq_xiRightMultiplicity` | `CCMPrimeGammaSourceDivisorTomography.lean` |
| RH iff source-tail continuation is analytic on `Re s > 1` | `riemannHypothesis_iff_primeGammaTailContinuation_analytic_rightOne` | `CCMPrimeGammaSourceDivisorTomography.lean` |
| Fixed-width pointwise positivity iff RH | `riemannHypothesis_iff_rectangular_logSample_weil_nonneg` | `CCMRectangularWeilCompleteness.lean` |
| Eventual lower boundedness iff RH | `riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow` | `CCMRectangularWeilCompleteness.lean` |
| Bounded norm iff RH | `riemannHypothesis_iff_rectangular_logSample_weil_norm_bdd` | `CCMRectangularTransverseGrowth.lean` |
| Exact norm power threshold | `xiRightTransverseSup_is_sharp_rectangular_power_exponent` | `CCMRectangularTransverseGrowth.lean` |
| One-sided loss exponent iff full Xi half-plane bound | `xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le` | `CCMRectangularOneSidedTransverseExponent.lean` |
| False-RH cofinal negative divergence | `not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below` | `CCMRectangularWeilCompleteness.lean` |
| False-RH two-sided subcritical power oscillation | `not_riemannHypothesis_implies_rectangular_weil_twoSided_power_oscillation` | `CCMRectangularTwoSidedOscillation.lean` |
| Sharp rectangular prime plus archimedean formula | `xiWeilPolarization_rectangular_eq_prime_add_arch` | `XiGuinandWeilRectangularFullFormula.lean` |
| Prime--Gamma logarithmic coefficient equals Weil sample | `xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re` | `CCMPrimeGammaSourceEnergySpectrum.lean` |
| RH iff prime--Gamma tail nonnegative | `riemannHypothesis_iff_primeGammaLogCoefficient_tail_nonneg` | `CCMPrimeGammaSourceEnergySpectrum.lean` |
| Prime--Gamma negative abscissa dichotomy | `xiRectangularPrimeGammaTailNegativePart_abscissa_dichotomy` | `CCMPrimeGammaSourceEnergySpectrum.lean` |
| Every Xi half-plane bound iff cumulative negative-mass growth | `xiZeroHalfPlaneBound_iff_primeGammaCumulativeNegativeMassGrowth` | `CCMCumulativeNegativeMassSpectrum.lean` |
| Exact false-RH cumulative power threshold | `primeGammaCumulativeNegativeMass_exactPowerOrder_of_not_rh` | `CCMCumulativeNegativeMassSpectrum.lean` |
| Critical cumulative law iff RH | `riemannHypothesis_iff_primeGammaCumulativeNegativeMassCriticalGrowth` | `CCMCumulativeNegativeMassSpectrum.lean` |
| Smooth generic set dense and residual | `xiSmoothProfileGenericSet_dense_residual` | `CCMSmoothTwoEdgeWeil.lean` |
| False-RH generic smooth cofinal lower divergence | `not_riemannHypothesis_implies_generic_smoothProfile_weil_cofinally_unbounded_below` | `CCMSmoothTwoEdgeWeil.lean` |
| Every individual generic smooth profile: positivity iff RH | `riemannHypothesis_iff_generic_smoothProfile_logSample_weil_nonneg` | `CCMSmoothTwoEdgeWeil.lean` |
| Every individual generic smooth profile: eventual lower bound iff RH | `riemannHypothesis_iff_generic_smoothProfile_logSample_weil_eventually_bddBelow` | `CCMSmoothTwoEdgeWeil.lean` |
| Smooth fixed-support pointwise positivity iff RH | `riemannHypothesis_iff_smoothProfile_logSample_weil_nonneg` | `CCMSmoothTwoEdgeWeil.lean` |
| Smooth fixed-support eventual lower boundedness iff RH | `riemannHypothesis_iff_smoothProfile_logSample_weil_eventually_bddBelow` | `CCMSmoothTwoEdgeWeil.lean` |
| Translated sector-Blaschke uniqueness | `frequency_zero_uniqueness_on_ray` | `FrequencySectorBlaschkeCompleteness.lean` |
| Arbitrary compact-carrier monomial completeness | `coordinate_pow_mem_closedSpan_frequencyLambertTangents` | `CompactCarrierFrequencyCompleteness.lean` |
| Reflected analytic odd Schwarz-real density | `criticalDisc_analytic_odd_schwarz_mem_realClosedSpan_frequencyLambert` | `CriticalDiscReflectedLambertUniversality.lean` |
| Pole-free genuine increment group contains full analytic fibre | `criticalDisc_analytic_odd_schwarz_mem_safeFrequencyIncrementGroup_closure` | `CriticalDiscReflectedLambertUniversality.lean` |
| Continuous safe-increment invariants are constant on fibre | `criticalDisc_continuous_safeFrequencyIncrementInvariant_eq_base` | `CriticalDiscReflectedLambertUniversality.lean` |
| Cofinite prime logs satisfy strong sector completeness | `cofinitePrimeLog_strongSectorBlaschkeComplete'` | `FrequencySectorBlaschkeCompleteness.lean` |
| Every even moment germ is exact normalization of a trace in cofinite prime orbit | `evenMomentGerm_cofinitePrimeLogOrbitClosure_and_normalizedTrace` | `ReflectedLambertRHBarrier.lean` |
| Every moment neighbourhood contains orbit-realized Hankel failure | `exists_close_frequencyOrbit_normalizedTraceHankel_failure` | `ReflectedLambertRHBarrier.lean` |
| No continuous safe-increment invariant Hankel classifier | `no_continuous_frequencyInvariant_traceHankel_classifier` | `ReflectedLambertRHBarrier.lean` |
| Source trace equals Xi logarithmic derivative | `continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain` | `GammaSewnMobiusXiWardJuliaTransport.lean` |
| Normalized source germ equals reciprocal-square moment germ | `normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm` | `PrimeArchCentralMomentGerm.lean` |
| Integer-polynomial source Hankel positivity iff RH | `reflectedLambert_sourceHankel_iff_RH` | `ReflectedLambertRHBarrier.lean` |

All modules live under:

`formal/GaloisForLFunctions/RHTower/`

## Hypothesis audit

- Width: every detector theorem assumes exactly `0 < L`.
- Sharp explicit formula: `0 ≤ L` and `L ≤ a`; paper applies it with `L > 0`.
- Arithmetic tail: cutoff hypothesis is
  `∀ n, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2`.
- One-sided exponent: exactly `0 ≤ alpha`.
- Two-sided oscillation: `¬RiemannHypothesis`, `0 ≤ alpha`, and
  `alpha < xiRightTransverseSup`.
- Smooth profiles: exactly `0 < eta` and `eta < L - eta`.
- Cumulative exact-order theorem: false RH is explicit, not inferred from a numerical witness.
- Local spectrum: injective, positive, strongly sector-Blaschke complete above a positive
  threshold; no arithmetic structure is assumed.
- Local carrier: `0 ≤ r₀ < r₁ < 1/2`; targets are analytic on the larger disc.
- Nonlinear local group: real parameter, arbitrarily prescribed positive radius, and strict
  Neumann norm `< 1`; all perturbed factors are genuinely invertible.
- Prime specialization: arbitrary finite prime deletion.

No paper theorem assumes:

- a rightmost zero;
- an attained transverse supremum;
- simple zeros;
- a zero-free transverse gap;
- numerical zero verification;
- a finite divisor;
- RH inside a premise advertised as unconditional.

## Source-purity audit

`xiRectangularPrimeGammaLogCoefficient` is defined by:

1. `rectangularPrimeAutocorrelationSum`, a finite von Mangoldt-weighted autocorrelation sum;
2. `normalizedRectangularBottomArchContribution`, an explicit Gamma--polar integral.

The source coefficient does not contain Xi zeros or `RiemannHypothesis` in its definition.
The divisor enters only through the proved explicit-formula equality.

## Paper-proof dependency audit

Paper supplies arguments for:

1. reciprocal-square summability and fixed-edge bounded remainder;
2. shifted-zeta carrier;
3. multiplicity-safe noncancellation at every shifted Xi pole;
4. cutoff-free full-observable continuation and exact normalized-residue recovery;
5. finite-prefix transfer of the complete polar divisor to the prime--Gamma source;
6. scale-local Landau contradiction without a maximal zero;
7. lower-loss and two-sided power classification;
8. sharp contour exhaustion and finite prime support;
9. nonnegative Dirichlet abscissa versus cumulative growth;
10. Baire residual simultaneous nonvanishing for smooth profiles;
11. translated sector-to-disc Blaschke zero uniqueness;
12. Lambert expansion, absolute M\"obius inversion, and Fourier--Borel recovery;
13. reflected polynomial and analytic Schwarz-real density;
14. pole-free Banach-algebra differentiation and infinitesimal repetition;
15. reciprocal-prime proof of cofinite prime-log completeness;
16. trace-class polynomial separation and integer Hankel reduction;
17. odd-to-even normalization and continuous-classifier contradiction.

No headline proof is deferred solely to Lean.

## Commands already passed

Each command was run sequentially in foreground from `formal/`:

```text
lake env lean GaloisForLFunctions/RHTower/CCM/CCMRectangularWeilCompleteness.lean
lake env lean GaloisForLFunctions/RHTower/CCM/CCMRectangularTransverseGrowth.lean
lake env lean GaloisForLFunctions/RHTower/CCM/CCMRectangularOneSidedTransverseExponent.lean
lake env lean GaloisForLFunctions/RHTower/CCM/CCMRectangularTwoSidedOscillation.lean
lake env lean GaloisForLFunctions/RHTower/XiGuinandWeilRectangularFullFormula.lean
lake env lean GaloisForLFunctions/RHTower/CCM/CCMPrimeGammaSourceEnergySpectrum.lean
lake env lean GaloisForLFunctions/RHTower/CCM/CCMPrimeGammaSourceDivisorTomography.lean
lake env lean GaloisForLFunctions/RHTower/CCM/CCMCumulativeNegativeMassSpectrum.lean
lake env lean GaloisForLFunctions/RHTower/CCM/CCMSmoothTwoEdgeWeil.lean
lake env lean GaloisForLFunctions/RHTower/FrequencySectorBlaschkeCompleteness.lean
lake env lean GaloisForLFunctions/RHTower/CompactCarrierFrequencyCompleteness.lean
lake env lean GaloisForLFunctions/RHTower/CriticalDiscReflectedLambertUniversality.lean
lake env lean GaloisForLFunctions/RHTower/ReflectedLambertRHBarrier.lean
```

All returned exit code `0`. `CCMRectangularTransverseGrowth.lean` emitted a non-fatal tactic
suggestion; no declaration failed.

Repository lint record below predates the combined manuscript and must be rerun:

```text
python3 scripts/formal_tools.py lint
```

Current final status is recorded only after the combined capstone audit.

## Axiom audit

Prior `#print axioms` audits of both theorem families found only:

```text
propext
Classical.choice
Quot.sound
```

These are standard Lean/mathlib logical axioms. No project axiom, `sorry`, `admit`, or unsafe
declaration appears in the theorem surface.

## Nonclaims

- Paper does not prove RH.
- Paper does not prove the critical cumulative source bound independently.
- Paper does not prove impossibility of CCM, Hilbert--Pólya, or another classical route.
- Paper does not claim general explicit-formula novelty.
- Candidate priority concerns exact fixed-width completeness plus source-spectrum package and
  remains subject to independent specialist review.
