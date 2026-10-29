# Arithmetic of square-root precision (ASRP)

- **ID:** asrp-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2910/fable.md §8 (also §3.4, §4.1, §7.3)
- **Statement:** precision classes of statements about weights, the battery as a classification,
  the integrality face of the count (exact floor, exponent = Θ), integer Dirichlet polynomials at
  arithmetic points, where precision is lost, calibration over 𝔽_q.

## Goal
Build `formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/` with umbrella and README.
Scope: HKT/AKL own Krein–Langer structure, CDG the Hecke defect, AET the section count, RAPT/AIT
the regulator; ASRP owns precision classes, integrality extraction and the transcendence toolkit
on integer Dirichlet polynomials, and states the precision class of the others' targets.

## Gates
- [x] 0 → 1  scope fixed, README first draft
- [x] modules 1–20 proved, checked, wired into `ArithmeticOfSquareRootPrecision.lean`; axioms audited
  (propext, Classical.choice, Quot.sound only)
- [ ] open topics of the README §9 (ceiling, off-line vanishing, positivity precision, inversion with
  arithmetic input, successor, index/defect/regulator precision, vertical zero estimates, structure)

## Module plan
1. `PrecisionClassesAndTheCount` — precision classes, count, stabilizer law, power threshold at ½.
2. `TheCountIsTheRiemannHypothesis` — each half is RH; θ(Λ) = Θ.
3. `TheBatteryOfTheCount` — visible/invisible moves, classification.
4. `TheDecidingInputTheorem` — parity, precision, aperture; PNT, GM, error laws precision-blind.
5. `TheIntegralityLatticeOfTheHorizon` — {∫₀¹P} = d_{n+1}⁻¹ℤ; min⁺ = 1/d_{n+1}.
6. `TheIntegralityExponentIsTheZeroWidth` — Siegel/Liouville halves at θ ⇔ Θ; RH ⇔ √-precise halves.
7. `IntegerDirichletPolynomialsAtArithmeticPoints` — D(k) lattice, D(−k) ∈ ℤ, real zeros < N, Siegel.
8. `TheLiouvilleTwinIsARatioOfHorizonTorsions` — A_λ(n) = 2ψ(√n) − ψ(n); reciprocal torsion.
9. `WherePrecisionIsLost` — Chebyshev–Möbius formula, Stirling precision, inversion amplification.
10. `CurvesCalibrateThePrecisionExponent` — exponent formula; golden; upper half blind to real zeros.
11. `TheGaugeStabilizerOfTheCount` — lower half monotone; a ≤ Λ: Count ⇔ RH ∧ Λ − a ∈ 𝒬; sign and
    torus gauges: Count ⇔ RH ∧ gauge distance O(√x log² x).
12. `ThePrecisionLedgerOfTheCount` — TFAE in eight currencies; Θ three readings; strip three readings.
13. `SupNormCeilingsForceVanishingAtSmallRationals` — b^n P(a/b) ∈ ℤ; sup-norm ceilings at precision
    θ < 1 force P(0) = P(½) = P(1) = 0.
14. `OneSignedPerturbations` — majorant/minorant principle; precision exponent = abscissa.
15. `TwoPrimeTowersSeeEveryOrdinateDifference` — Liouville/Baker/Dirichlet separation; two-prime
    non-aliasing at polynomial precision (uses `RHTower.Matveev.effectiveBakerBound_holds`).
16. `MonotoneErrorsInvertAtMertensPrecision` — Abel bound; RH ⇔ √-precise monotone inversion.
17. `TowerPositivityIsPrecisionExact` — tower index zero ⇒ count; stabilizer {0} vs 𝒬.
18. `TheStirlingErrorSplits` — log⌊y⌋! = F + monotone + sawtooth; ψ − I(F) − I(h) = O(log n · max|M|).
19. `TheSmoothTermInvertsToMobiusMoments` — I_x(F) = x((log x − 1)m − ℓ); |I_n(h)| < n; arithmetic ledger.
20. `FiniteAperturePositivityCannotDecide` — window law; aperture positivity ⊆ count ⇒ ¬RH; 3/10 weight-blind.

## No-go closure
- **Inversion no-go** (`not_inversion_bounded`): size bounds do not survive Möbius inversion.
  Survivor: monotone errors invert at exactly Mertens precision (`riemannHypothesis_iff_monotone_inversion`);
  the Stirling error splits so that only the smooth term and the sawtooth remain (`abs_psi_sub_smooth_sub_sawtooth_le`). Lean: done.
- **Integrality "linear floor"**: refuted as stated; the floor is exact and the integrality exponent is Θ
  (`siegelExponent_eq_zeroReSup`). Survivor for ceilings: sup-norm certificates vanish at 0, ½, 1
  (`eventually_vanish_of_supCeiling`). Lean: done.
- **One-prime certification**: one tower aliases (`one_prime_aliases`). Survivor: two towers certify at
  polynomial margin (`two_prime_alias_bound_in_Δ`). Lean: done.

## Leads checked (exist; do not redo)
- Exponent law Θ: `RHTower.chebyshevPsi_sub_exponent_law`, one-sided lower power bound ⇒ zeros:
  `RHTower.re_le_half_add_of_chebyshevError_ge_rpow`.
- Upper one-sided count ⇔ RH: HKT `negIndex_zetaKernel_eq_zero_iff_count`.
- Von Koch: `RHTower.riemannHypothesis_iff_chebyshevPsi_sub_isBigO`; PNT: `RHTower.tendsto_chebyshevPsiReal_div`.
- GM unconditional: `RHTower.tendsto_psi_short_window_div_seventeenThirtieths`.
- Nair/integrality: AET `TheStepanovMethodOverZ`.
- Real zeros of exponential polynomials: `HTGeometry.ExpZeroBound.card_lt_of_expPoly_eq_zero`.
- Curve data: ACS `CurveDatum`, `goldenDatum`; HKT `global_law_count`.

## Log
- 2026-10-29 — created; README first draft written.
- 2026-10-29 — modules 1–20 formalized; README rewritten on the established results.
