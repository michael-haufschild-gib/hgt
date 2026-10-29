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
- [x] modules 1–10 proved, umbrella `ArithmeticOfSquareRootPrecision.lean`
- [ ] modules 11–13 (gauge stabilizer, ledger, sup-norm vanishing) compiled and wired

## Module plan
1. `PrecisionClassesAndTheCount` — partial sums, precision classes, count, stabilizer law, power
   threshold at η = ½ (inclusive).
2. `TheBatteryOfTheCount` — λΛ and cΛ visible; finite modifications, Euler-factor deletions, tower
   flips invisible; cofinite flips visible.
3. `TheDecidingInputTheorem` — parity, precision, aperture; producers precision-blind (PNT, GM).
4. `PrecisionExponentIsTheZeroWidth` — θ(Λ) = Θ; one-signed exponent = abscissa.
5. `TheIntegralityLatticeOfTheHorizon` — {∫₀¹P} = d_{n+1}⁻¹ℤ; min⁺ = 1/d_{n+1}.
6. `TheIntegralityExponentIsTheZeroWidth` — Siegel/Liouville halves at θ ⇔ Θ; RH ⇔ √-precise halves.
7. `IntegerDirichletPolynomialsAtArithmeticPoints` — D(k) lattice d_N^{-k}ℤ, D(−k) ∈ ℤ,
   Vandermonde, real zeros < N, Siegel's lemma.
8. `TheLiouvilleTwinHasReciprocalTorsion`.
9. `WherePrecisionIsLost` — Chebyshev transform, Stirling precision, inversion amplification.
10. `CurvesCalibrateThePrecisionExponent`.
11. `TheGaugeStabilizerOfTheCount` — lower half monotone; a ≤ Λ: Count ⇔ RH ∧ Λ − a ∈ 𝒬; sign and
    torus gauges: Count ⇔ RH ∧ gauge distance O(√x log² x).
12. `ThePrecisionLedgerOfTheCount` — TFAE in eight currencies; Θ three readings; strip three readings.
13. `SupNormCeilingsForceVanishingAtSmallRationals` — b^n P(a/b) ∈ ℤ; sup-norm ceilings at precision
    θ < 1 force P(0) = P(½) = P(1) = 0.

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
