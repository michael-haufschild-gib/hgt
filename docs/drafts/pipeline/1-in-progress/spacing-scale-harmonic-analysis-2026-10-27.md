# Arithmetic harmonic analysis at the spacing scale (SSHA)

- **ID:** ssha
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for SH1–SH8; open core below
- **Source:** docs/reports/review-2710/obstacles-summary.md §4 (Q1 B3.25/B3.26, Q2 B3.16, Q3 B3.24)
- **Statement:** Programme `formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/` (README there).

## Goal
Answer Q1 at the spacing (B3.25), the overlap question (B3.26), and locate the gauge (Q2).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  SH1–SH8 proved on paper
- [x] 2 → 3  SH1–SH8 formalized (`lake --old env lean`, axioms: propext, Classical.choice, Quot.sound)

## Proved (Lean)
- SH4 `re_W_add_sinh_sq_nonneg_spacing`: `Re W + 2S² ≥ 0` on atomic tests of width `≤ c₀ δ_N`, all `N` (B3.25 with `c = c₀`); gauge blind (`twinMarkov_atomicTest_nonneg_spacing`).
- SH5 `diamagnetic_inequality`, `twinMarkov_ge_of_markov_ge`.
- SH6 `riemannHypothesis_iff_splineAtomic_negIndex_eq_zero`: fixed width (unbounded overlap) is RH.
- SH7 `twistedPrimeSum_sub_primeSum_gauge_eq`: gauge defect lives on non-ratio lags.
- SH8 `paperFT_atomicTest`, `Wsummand_atomicTest_onLine`.

## Open core
1. Intermediate exponents `w = N^{−θ}`, `0 < θ < 1`: paper argument (log-lattice Riemann sums + continuity of `W`) gives RH-strength; needs a quantitative continuity of `W` in Lean.
2. Bounded overlap ratio: finite-aperture problem.
3. Critical constant `c*`: on the pole vector the finite part of `M` is `log(1/c) + κ₀(g) + γ + O(c)`.
4. Gauge form margin at bounded overlap via non-ratio lags.

## Log
- 2026-10-27 — created; SH1–SH8 formalized.
