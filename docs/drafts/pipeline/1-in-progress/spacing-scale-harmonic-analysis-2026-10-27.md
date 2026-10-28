# Arithmetic harmonic analysis at the spacing scale (SSHA)

- **ID:** ssha
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for SH1–SH22; open core below
- **Source:** docs/reports/review-2710/obstacles-summary.md §4 (Q1 B3.25/B3.26, Q2 B3.16, Q3 B3.24)
- **Statement:** Programme `formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/` (README there).

## Goal
Answer Q1 at the spacing (B3.25), the overlap question (B3.26), and locate the gauge (Q2).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  SH1–SH22 proved on paper
- [x] 2 → 3  SH1–SH22 formalized (`lake --old env lean`, axioms: propext, Classical.choice, Quot.sound)

## Proved (Lean)
- SH4 `re_W_add_sinh_sq_nonneg_spacing`: `Re W + 2S² ≥ 0` on atomic tests of width `≤ c₀ δ_N`, all `N` (B3.25 with `c = c₀`); gauge blind (`twinMarkov_atomicTest_nonneg_spacing`).
- SH5 `diamagnetic_inequality`, `twinMarkov_ge_of_markov_ge`.
- SH6 `riemannHypothesis_iff_splineAtomic_negIndex_eq_zero`: fixed width (unbounded overlap) is RH.
- SH7 `twistedPrimeSum_sub_primeSum_gauge_eq`: gauge defect lives on non-ratio lags.
- SH8 `paperFT_atomicTest`, `Wsummand_atomicTest_onLine`.
- SH11 `riemannHypothesis_iff_atomicFamilies_nonneg_of_growth`: RH-strength once overlap ratio ≫ √log N (θ* = 1, B3.26; `_log` at (log N)^α, α > 1/2).
- SH12 `atomicFamilies_negative_iff`: under overlap growth a bounded twist is seen iff not Weil positive (Liouville, cΛ, quadratic mixtures).
- SH13 `markovThreshold_bracket`, `riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg`: Markov law universal to c₀, fails for ζ under overlap growth; one negative square iff RH (K_univ bracketed).
- SH14 `norm_Wsummand_atomicTest_dilate_le`: one zero weighs ≤ m_ρ·overlap·(‖φ‖₁²/‖φ‖₂²)/(2√(β(1−β))) of the diagonal energy.
- SH15 `markov_poleVector_negative_inside_separated`, `archRobinConstant_eq`: 2c_∞ = 2log2 + π/2; M alone < 0 on the pole vector at width cδ_N for c > e^{β/‖φ‖²}/(2π); c₀ ≤ c*_M ≤ e/(2π).
- SH16 `universalThreshold_bracket`: c₀ ≤ K_univ < ∞ (wide dipole on atoms 1, 2 against the aligned sign twist) — W26.
- SH17 `primeSum_atomicTest_eq_ratio_add`, `abs_nonRatioForm_le`, `primeSum_atomicTest_le_rows`: prime form at ratio K as row sums; non-ratio rows O(K) + O(K(m/N)log m); gauge-defect summability discharged — W12.
- SH18 `riemannHypothesis_iff_atomicFamilies_nonneg_of_growthTwo`, `_log_quarter`: trapezoid weights F(a_j)(a_{j+1}−a_{j−1})/2 make the synthesis error (k/n₀)²; RH-strength once overlap ratio ≫ (log N)^{1/4} (C² profiles).
- SH19 `riemannHypothesis_iff_atomicFamilies_nonneg_of_growthPow`, `_log_pos`: Euler–Maclaurin weights F(log n − c)/n (corpus `dqpt_euler_maclaurin`) give error O((k/n₀)^p) every p for smooth profiles; mollification gives smooth negative tests; RH-strength at overlap (log N)^ε, every ε > 0 — W22.
- SH20 `StableForm`, `atomicFamilies_negative_iff_of_growthPow`, `markov_atomicFamilies_negative_of_growthPow`: twins seen and Markov negative square at every root.
- SH21 `riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg_of_growthPow`: pole hyperplane criterion at every root (correction by a synthesized bump).
- SH22 `riemannHypothesis_iff_atomicFamilies_nonneg_of_gevrey`, `riemannHypothesis_iff_gevreyProfile_nonneg_loglog`: Gevrey profiles of class s give RH-strength beyond (log log N)^s; explicit Gevrey-2 profile c·E(1+x)E(1−x) ⇒ (log log N)^α, α > 2 (card 3-formalized/ssha-gevrey-window-2026-10-28).

## Open core
1. Window between c₀ and (log log N)^s (SH22; explicit s = 2): Denjoy–Carleman profiles of class s → 1+; sharp threshold A(ϱ) log N ≍ 1; Nyquist penalty at fixed ϱ.
2. Critical constant: c*_M itself (cross-term density on the pole vector, optimal profile); c* of Re W + 2S².
3. Gauge form margin at bounded overlap via non-ratio lags.
4. Interior anti-alignment (Q3).

## Log
- 2026-10-27 — created; SH1–SH8 formalized.
- 2026-10-28 — SH9–SH12 (Lévy continuity, log-lattice synthesis, critical exponent, gauge visibility) formalized.
