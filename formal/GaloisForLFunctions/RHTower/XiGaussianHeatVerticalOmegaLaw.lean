import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalVarianceLaw
import GaloisForLFunctions.RHTower.XiGaussianHeatPrimeChirpReceiver
import GaloisForLFunctions.RHTower.XiStripEdgeHeightFloorRatioGate
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalExponentialType

/-!
# The square-root size of the prime chirp is sharp, unconditionally

On one vertical line `Re τ = a`, RH is equivalent to `S(τ) = O(|τ|^{1/2})` for the Gaussian–von
Mangoldt chirp `S(τ) = Σ Λ(n) n^{-1/2} exp(-(log n)²/(4τ))`
(`riemannHypothesis_iff_gaussianPrimeChirpSum_le_sqrt_norm`).  This module shows that the order
`|τ|^{1/2}` cannot be improved, without assuming RH.

**Theorem** (`not_tendsto_zero_xiGaussianHeatTraceC`).  For every `a > 0`, the heat trace
`ν(a + ib)` does not tend to `0` as `b → ∞`.

**Corollary** (`exists_frequently_le_norm_gaussianPrimeChirpSum_sub_main`).  There is `ε > 0` with
`‖S(a+ib) - M(a+ib)‖ ≥ ε |a+ib|^{1/2}` for arbitrarily large `b`, where
`M(τ) = (Arch(τ) + 2π e^{τ/4}) / (π/τ)^{1/2}` is the explicit archimedean and pole part.  This is the
HCF analogue of `ψ(x) - x = Ω(√x)`.

Proof.  Suppose `ν(a+ib) → 0`.  Conjugation symmetry (`ν(a - ib) = conj ν(a + ib)`) and continuity
make `ν` bounded on the whole line, so RH holds
(`riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line`).  Under RH the Cesàro means
of `‖ν‖²` converge to the coincidence sum (`tendsto_xiGaussianHeatVerticalVariance_of_rh`).  That sum
is at least `Σ_q e^{-2aλ_q} > 0` (`tsum_diag_le_vertical_variance_limit`), while `ν → 0` forces the
means to `0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Conjugation symmetry of the heat trace in complex time. -/
theorem xiGaussianHeatTraceC_conj (τ : ℂ) :
    xiGaussianHeatTraceC ((starRingEnd ℂ) τ) = (starRingEnd ℂ) (xiGaussianHeatTraceC τ) := by
  rw [xiGaussianHeatTraceC, xiGaussianHeatTraceC, Complex.conj_tsum,
    ← xiZeroCopyLineConjEquiv.tsum_eq]
  refine tsum_congr fun q => ?_
  rw [xiGaussianHeatTermC, xiGaussianHeatTermC, xiSpectralPoint_lineConj, ← Complex.exp_conj]
  congr 1
  simp [map_pow]

theorem continuous_xiGaussianHeatTraceC_vertical {a : ℝ} (ha : 0 < a) :
    Continuous (fun b : ℝ => xiGaussianHeatTraceC ((a : ℂ) + b * I)) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hτ : 0 < ((a : ℂ) + b * I).re := by simpa using ha
  exact ContinuousAt.comp (g := xiGaussianHeatTraceC) (f := fun b : ℝ => (a : ℂ) + b * I)
    (differentiableAt_xiGaussianHeatTraceC hτ).continuousAt (by fun_prop)

/-- Cesàro means of a nonnegative continuous function tending to `0` tend to `0`. -/
theorem tendsto_cesaro_integral_zero {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ b, 0 ≤ f b)
    (hlim : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun B : ℝ => (1 / B) * ∫ b in (0 : ℝ)..B, f b) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B₁, hB₁⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (by linarith)
  set B₁' : ℝ := max B₁ 0
  set M : ℝ := ∫ b in (0 : ℝ)..B₁', f b
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (le_max_right _ _) fun b _ => h0 b
  refine ⟨max (B₁' + 1) (2 * M / ε + 1), fun B hB => ?_⟩
  have hB1 : B₁' + 1 ≤ B := (le_max_left _ _).trans hB
  have hB2 : 2 * M / ε + 1 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := by linarith [le_max_right B₁ 0]
  have hsplit : (∫ b in (0 : ℝ)..B, f b) = M + ∫ b in B₁'..B, f b :=
    (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  have htail : (∫ b in B₁'..B, f b) ≤ ε / 2 * (B - B₁') := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := B₁') (b := B) (C := ε / 2)
      (f := f) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        have := hB₁ x ((le_max_left _ _).trans hx.1.le)
        rw [Real.dist_eq, sub_zero] at this
        exact this.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ B - B₁')] at h
    exact (le_abs_self _).trans h
  have htail0 : 0 ≤ ∫ b in B₁'..B, f b :=
    intervalIntegral.integral_nonneg (by linarith) fun b _ => h0 b
  have hI0 : 0 ≤ ∫ b in (0 : ℝ)..B, f b := intervalIntegral.integral_nonneg hBpos.le fun b _ => h0 b
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (by positivity) hI0), hsplit]
  have hMB : M / B < ε / 2 := by
    rw [div_lt_iff₀ hBpos]
    have : 2 * M / ε < B := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  have hBB : (1 / B) * (ε / 2 * (B - B₁')) ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hBpos]
    nlinarith [le_max_right B₁ 0]
  have htailB : (1 / B) * (∫ b in B₁'..B, f b) ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left htail (by positivity)).trans hBB
  calc 1 / B * (M + ∫ b in B₁'..B, f b) = M / B + (1 / B) * ∫ b in B₁'..B, f b := by ring
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hMB htailB
    _ = ε := by ring

/-- **Unconditional non-decay of the vertical heat trace.** -/
theorem not_tendsto_zero_xiGaussianHeatTraceC {a : ℝ} (ha : 0 < a) :
    ¬ Tendsto (fun b : ℝ => xiGaussianHeatTraceC ((a : ℂ) + b * I)) atTop (𝓝 0) := by
  intro hlim
  have hcont := continuous_xiGaussianHeatTraceC_vertical ha
  -- boundedness on the whole line, hence RH
  have hRH : RiemannHypothesis := by
    rw [riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha]
    obtain ⟨B₀, hB₀⟩ := Metric.tendsto_atTop.1 hlim 1 one_pos
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := -|B₀|) (b := |B₀|)).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨max K 1, fun b => ?_⟩
    rcases le_or_gt |B₀| |b| with hbig | hsmall
    · rcases le_or_gt 0 b with hb | hb
      · have := hB₀ b (by rw [abs_of_nonneg hb] at hbig; exact (le_abs_self B₀).trans hbig)
        rw [dist_zero_right] at this
        exact le_max_of_le_right this.le
      · have hsym : xiGaussianHeatTraceC ((a : ℂ) + b * I) =
            (starRingEnd ℂ) (xiGaussianHeatTraceC ((a : ℂ) + (-b : ℝ) * I)) := by
          rw [← xiGaussianHeatTraceC_conj]
          congr 1
          apply Complex.ext <;> simp
        rw [hsym, Complex.norm_conj]
        have := hB₀ (-b) (by rw [abs_of_neg hb] at hbig; exact (le_abs_self B₀).trans hbig)
        rw [dist_zero_right] at this
        exact le_max_of_le_right this.le
    · exact le_max_of_le_left (hK b ⟨by linarith [neg_abs_le b, abs_nonneg b],
        by linarith [le_abs_self b]⟩)
  -- under RH the Cesàro means of `‖ν‖²` converge to a positive limit
  have hlaw := tendsto_xiGaussianHeatVerticalVariance_of_rh hRH ha
  have hsq : Tendsto (fun b : ℝ => ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ^ 2) atTop (𝓝 0) := by
    have := (continuous_norm.tendsto (0 : ℂ)).comp hlim
    simpa using this.pow 2
  have hces := tendsto_cesaro_integral_zero (hcont.norm.pow 2) (fun b => sq_nonneg _) hsq
  have heq := tendsto_nhds_unique hlaw hces
  have hdiag := tsum_diag_le_vertical_variance_limit ha
  rw [heq] at hdiag
  have hsumm : Summable (fun q : XiZeroCopy =>
      Real.exp (-(a * xiSpectralSqRe q)) * Real.exp (-(a * xiSpectralSqRe q))) := by
    have h := summable_norm_xiGaussianHeatTermC (τ := ((2 * a : ℝ) : ℂ)) (by simpa using ha)
    refine h.congr fun q => ?_
    rw [norm_xiGaussianHeatTermC, ← Real.exp_add]
    simp [xiSpectralSqRe]
    ring_nf
  obtain ⟨q₀⟩ := xiZeroCopy_nonempty
  have hpos := hsumm.tsum_pos (fun q => by positivity) q₀ (by positivity)
  linarith

/-- The prime chirp minus its explicit main part is `-√(πτ)·ν`, in norm. -/
theorem norm_gaussianPrimeChirpSum_sub_main {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ‖gaussianPrimeChirpSum ((a : ℂ) + b * I) -
        (gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I)) /
          ((Real.pi : ℂ) / ((a : ℂ) + b * I)) ^ (1 / 2 : ℂ)‖ =
      Real.sqrt Real.pi * Real.sqrt ‖(a : ℂ) + b * I‖ *
        ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ := by
  set τ : ℂ := (a : ℂ) + b * I
  have hτre : 0 < τ.re := by simpa [τ] using ha
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτre; simp at hτre
  have hne : (Real.pi : ℂ) / τ ≠ 0 := div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hτ0
  have hp0 : ((Real.pi : ℂ) / τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).2 hne
  have hpnorm : ‖((Real.pi : ℂ) / τ) ^ (1 / 2 : ℂ)‖ = Real.sqrt Real.pi / Real.sqrt ‖τ‖ := by
    rw [Complex.norm_cpow_of_ne_zero hne]
    have him : (1 / 2 : ℂ).im = 0 := by norm_num
    have hre2 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [him, hre2, mul_zero, Real.exp_zero, div_one, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Real.div_rpow Real.pi_pos.le (norm_nonneg _),
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hid := pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime hτre
  have hdiff : gaussianPrimeChirpSum τ -
      (gaussianArchCriticalC τ + gaussianArchPoleC τ) / ((Real.pi : ℂ) / τ) ^ (1 / 2 : ℂ) =
        -((Real.pi : ℂ) * xiGaussianHeatTraceC τ) / ((Real.pi : ℂ) / τ) ^ (1 / 2 : ℂ) := by
    rw [hid, gaussianPrimeChirpC]
    field_simp
    ring
  rw [hdiff, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, hpnorm]
  have hsq : 0 < Real.sqrt ‖τ‖ := Real.sqrt_pos.2 (norm_pos_iff.2 hτ0)
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  calc Real.pi * ‖xiGaussianHeatTraceC τ‖ / (Real.sqrt Real.pi / Real.sqrt ‖τ‖)
      = (Real.sqrt Real.pi * Real.sqrt Real.pi) * ‖xiGaussianHeatTraceC τ‖ /
          (Real.sqrt Real.pi / Real.sqrt ‖τ‖) := by
        rw [Real.mul_self_sqrt Real.pi_pos.le]
    _ = Real.sqrt Real.pi * Real.sqrt ‖τ‖ * ‖xiGaussianHeatTraceC τ‖ := by
        field_simp

/-- **Unconditional Ω-law for the prime chirp.**  For every `a > 0` there is `ε > 0` such that
`‖S(a+ib) - M(a+ib)‖ ≥ ε |a+ib|^{1/2}` for arbitrarily large `b`. -/
theorem exists_frequently_le_norm_gaussianPrimeChirpSum_sub_main {a : ℝ} (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ b : ℝ in atTop,
      ε * Real.sqrt ‖(a : ℂ) + b * I‖ ≤
        ‖gaussianPrimeChirpSum ((a : ℂ) + b * I) -
          (gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I)) /
            ((Real.pi : ℂ) / ((a : ℂ) + b * I)) ^ (1 / 2 : ℂ)‖ := by
  have hnot := not_tendsto_zero_xiGaussianHeatTraceC ha
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨δ, hδ, hfreq⟩ := hnot
  refine ⟨Real.sqrt Real.pi * δ, by positivity, ?_⟩
  rw [Filter.frequently_atTop]
  intro B
  obtain ⟨b, hb, hbig⟩ := hfreq B
  refine ⟨b, hb, ?_⟩
  rw [norm_gaussianPrimeChirpSum_sub_main ha b]
  rw [dist_zero_right] at hbig
  have hsq : 0 ≤ Real.sqrt ‖(a : ℂ) + b * I‖ := Real.sqrt_nonneg _
  have hspi : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  calc Real.sqrt Real.pi * δ * Real.sqrt ‖(a : ℂ) + b * I‖
      = Real.sqrt Real.pi * Real.sqrt ‖(a : ℂ) + b * I‖ * δ := by ring
    _ ≤ Real.sqrt Real.pi * Real.sqrt ‖(a : ℂ) + b * I‖ *
          ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ :=
        mul_le_mul_of_nonneg_left hbig (mul_nonneg hspi hsq)

/-- **Gap law.**  On one vertical line the prime chirp has no intermediate growth.  Either
`S(a+ib) = O(|a+ib|^{1/2})` (this is RH), or for some `ε > 0` it is not
`O(|a+ib|^{1/2} e^{ε|b|})`.  Polynomial or `exp(o(|b|))` growth beyond `|b|^{1/2}` is impossible. -/
theorem gaussianPrimeChirpSum_growth_gap {a : ℝ} (ha : 0 < a) :
    (∃ C : ℝ, ∀ b : ℝ,
        ‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ ≤ C * Real.sqrt ‖(a : ℂ) + b * I‖) ∨
      ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, ∃ b : ℝ, C * Real.sqrt ‖(a : ℂ) + b * I‖ * Real.exp (ε * |b|) <
        ‖gaussianPrimeChirpSum ((a : ℂ) + b * I)‖ := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ((riemannHypothesis_iff_gaussianPrimeChirpSum_le_sqrt_norm ha).1 hRH)
  · right
    have h := mt (riemannHypothesis_iff_gaussianPrimeChirpSum_subexponential ha).2 hRH
    push Not at h
    obtain ⟨ε, hε, hC⟩ := h
    exact ⟨ε, hε, hC⟩

end

end RHTower
