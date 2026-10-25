import GaloisForLFunctions.RHTower.ZetaSmoothedLandauFormula

/-!
# A smoothed Riemann–von Mangoldt formula

For a `C²` profile `w` supported in `[−1, 1]` and `T ≥ 2`,

`Σ_ρ m_ρ ŵ(γ_ρ/T) = T w(0) log T + c_w T + O(1)`,   `c_w = (1/2π) ∫ ŵ(s) log(|s|/2π) ds`,

over all nontrivial zeros, `γ_ρ = (ρ − ½)/i` (`exists_smoothedZeroCount`).  This is Weil's
explicit formula for the dilated test `k(u) = T w(Tu)`: the prime side is empty (`T log 2 > 1`), the
poles are `O(‖w‖₁)`, and the Gamma term `∫ ŵ(τ/T) μ(τ) dτ` splits as the Stirling main term
`(1/2π) log(|τ|/2π)`, which scales to `T w(0) log T + c_w T` (using `∫ ŵ = 2π w(0)`), plus the
integrable remainder `muRem`, which contributes at most `sup|ŵ| · ‖muRem‖₁`.
-/

open Complex MeasureTheory Real Set
open scoped Real FourierTransform

noncomputable section

namespace RHTower

open Zeta23

/-! ## Functions with a logarithmic singularity at `0` and `|s|^{-3/2}` decay -/

/-- A function bounded by `A|log s| + B₁` on `(−1, 1]` and by `B₂ (1 + |s|)^{−3/2}` for `|s| ≥ 1` is
integrable. -/
lemma integrable_of_log_near_zero {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f) {A B₁ B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (hin : ∀ s ∈ Ioc (-1 : ℝ) 1, ‖f s‖ ≤ A * |Real.log s| + B₁)
    (hout : ∀ s : ℝ, 1 ≤ |s| → ‖f s‖ ≤ B₂ * (1 + |s|) ^ (-(3 / 2 : ℝ))) :
    Integrable f := by
  have hlog : IntegrableOn (fun s : ℝ => A * |Real.log s| + B₁) (Ioc (-1 : ℝ) 1) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).1
    exact (h.norm.const_mul A).add (integrableOn_const (by simp))
  have hdecay : Integrable (fun s : ℝ => B₂ * (1 + |s|) ^ (-(3 / 2 : ℝ))) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num)
    simpa [Real.norm_eq_abs] using this.const_mul B₂
  refine ((hlog.integrable_indicator measurableSet_Ioc).add hdecay).mono' hf
    (Filter.Eventually.of_forall fun s => ?_)
  have hd : 0 ≤ B₂ * (1 + |s|) ^ (-(3 / 2 : ℝ)) := mul_nonneg hB₂ (Real.rpow_nonneg (by positivity) _)
  by_cases hs : s ∈ Ioc (-1 : ℝ) 1
  · rw [Pi.add_apply, indicator_of_mem hs]
    linarith [hin s hs]
  · rw [Pi.add_apply, indicator_of_notMem hs, zero_add]
    refine hout s ?_
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hs
    rcases hs with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- `1/τ² ≤ 4(1 + |τ|)^{−3/2}` for `|τ| ≥ 1`. -/
lemma inv_sq_le_rpow {τ : ℝ} (hτ : 1 ≤ |τ|) : 1 / τ ^ 2 ≤ 4 * (1 + |τ|) ^ (-(3 / 2 : ℝ)) := by
  rw [one_add_abs_rpow_neg_three_halves, mul_one_div,
    div_le_div_iff₀ (by nlinarith [sq_abs τ]) (by positivity)]
  set q := Real.sqrt (1 + |τ|) with hq
  have hq2 : q ^ 2 = 1 + |τ| := Real.sq_sqrt (by positivity)
  have hq1 : q ≤ 1 + |τ| := by nlinarith [Real.sqrt_nonneg (1 + |τ|)]
  have : (1 + |τ|) * q ≤ (1 + |τ|) ^ 2 := by nlinarith [abs_nonneg τ]
  nlinarith [sq_abs τ]

/-- `(2√t + c)/(1 + t²) ≤ 2(2 + c)(1 + t)^{−3/2}` for `t ≥ 0`, `c ≥ 0`. -/
lemma sqrt_add_div_le_rpow {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    (2 * Real.sqrt t + c) / (1 + t ^ 2) ≤ 2 * (2 + c) * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
  rw [one_add_abs_rpow_neg_three_halves, abs_of_nonneg ht, mul_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  set q := Real.sqrt (1 + t) with hq
  have hq2 : q ^ 2 = 1 + t := Real.sq_sqrt (by linarith)
  have hq1 : 1 ≤ q := Real.one_le_sqrt.mpr (by linarith)
  have hst : Real.sqrt t ≤ q := Real.sqrt_le_sqrt (by linarith)
  have h1 : 2 * Real.sqrt t + c ≤ (2 + c) * q := by nlinarith [Real.sqrt_nonneg t]
  have h2 : (2 * Real.sqrt t + c) * ((1 + t) * q) ≤ (2 + c) * (1 + t) ^ 2 := by
    calc (2 * Real.sqrt t + c) * ((1 + t) * q) ≤ (2 + c) * q * ((1 + t) * q) := by
          gcongr
      _ = (2 + c) * (1 + t) * q ^ 2 := by ring
      _ = (2 + c) * (1 + t) ^ 2 := by rw [hq2]; ring
  nlinarith [sq_nonneg (1 - t)]

/-- `|log(|s|/2π)| ≤ |log s| + log 2π`. -/
lemma abs_log_abs_div_two_pi_le (s : ℝ) :
    |Real.log (|s| / (2 * π))| ≤ |Real.log s| + Real.log (2 * π) := by
  have hl : 0 < Real.log (2 * π) := Real.log_pos (by linarith [Real.pi_gt_three])
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [abs_zero, zero_div, Real.log_zero, abs_zero]; linarith
  · rw [Real.log_div (abs_ne_zero.mpr hs) (by positivity), Real.log_abs]
    calc |Real.log s - Real.log (2 * π)| ≤ |Real.log s| + |Real.log (2 * π)| := abs_sub _ _
      _ = _ := by rw [abs_of_pos hl]

/-! ## The Gamma density after its Stirling main term -/

/-- The remainder `μ(τ) − (1/2π) log(|τ|/2π)` of the Gamma density. -/
def muRem (τ : ℝ) : ℝ := mu τ - (1 / (2 * π)) * Real.log (|τ| / (2 * π))

/-- The remainder of the Gamma density is integrable: `O(1/τ²)` at infinity, logarithmic at `0`. -/
theorem integrable_muRem : Integrable muRem := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    gammaFacts.smooth.continuous.continuousOn
  have hπ : 0 < 2 * π := by positivity
  have hπ1 : 1 / (2 * π) ≤ 1 := by rw [div_le_one hπ]; linarith [Real.pi_gt_three]
  have hmeas : AEStronglyMeasurable muRem := by
    refine (gammaFacts.smooth.continuous.measurable.sub
      (measurable_const.mul ?_)).aestronglyMeasurable
    exact Real.measurable_log.comp (measurable_id.abs.div_const _)
  refine integrable_of_log_near_zero hmeas (A := 1) (B₁ := B + Real.log (2 * π))
    (B₂ := 4 * |C|) (by positivity) (fun s hs => ?_) (fun s hs => ?_)
  · have hs' : s ∈ Icc (-1 : ℝ) 1 := Ioc_subset_Icc_self hs
    have h1 := hB s hs'
    rw [Real.norm_eq_abs] at h1 ⊢
    have h2 := abs_log_abs_div_two_pi_le s
    have h3 : |(1 / (2 * π)) * Real.log (|s| / (2 * π))| ≤ |Real.log (|s| / (2 * π))| := by
      rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_of_le_one_left (abs_nonneg _) hπ1
    calc |muRem s| ≤ |mu s| + |(1 / (2 * π)) * Real.log (|s| / (2 * π))| := abs_sub _ _
      _ ≤ _ := by linarith
  · rw [Real.norm_eq_abs]
    have h1 := hC s hs
    have h2 := inv_sq_le_rpow hs
    have hτ2 : 0 < s ^ 2 := by nlinarith [sq_abs s]
    calc |muRem s| ≤ C / s ^ 2 := h1
      _ ≤ |C| * (1 / s ^ 2) := by rw [mul_one_div]; gcongr; exact le_abs_self C
      _ ≤ |C| * (4 * (1 + |s|) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by ring

/-! ## The transform of the profile on the real axis -/

section Profile

variable {w : ℝ → ℂ}

lemma integrable_and_smul (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    Integrable w ∧ Integrable (fun x : ℝ => x • w x) :=
  ⟨hw.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs hsupp),
    (continuous_id.smul hw.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (Λ := 1) fun u hu =>
        hsupp u fun h => hu (by simp [h]))⟩

lemma continuous_paperFT_ofReal' (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    Continuous (fun s : ℝ => paperFT w s) :=
  continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_paperFT_ofReal (integrable_and_smul hw hsupp).1
      (integrable_and_smul hw hsupp).2 s).continuousAt

lemma integrable_paperFT_ofReal' (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    Integrable (fun s : ℝ => paperFT w s) := by
  obtain ⟨C, -, hC⟩ := exists_paperFT_decay hw hsupp
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    (continuous_paperFT_ofReal' hw hsupp).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  rw [← div_eq_mul_inv]
  exact (hC s).1

/-- Fourier inversion at `0`: `∫ ŵ = 2π w(0)`. -/
theorem integral_paperFT_ofReal (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ∫ s : ℝ, paperFT w s = 2 * π * w 0 := by
  have hFk : Integrable (𝓕 w) := by
    have h := (integrable_paperFT_ofReal' hw hsupp).comp_mul_left' (R := -(2 * π)) (by
      have := Real.pi_pos; intro h; linarith)
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [fourier_eq_paperFT]
    push_cast; ring_nf
  have h := EF.paper_inversion hw.continuous (integrable_and_smul hw hsupp).1 hFk 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [h]; field_simp

/-- The log-weighted transform `ŵ(s) log(|s|/2π)` is integrable. -/
theorem integrable_paperFT_mul_log (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    Integrable (fun s : ℝ => paperFT w s * (Real.log (|s| / (2 * π)) : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_paperFT_decay hw hsupp
  have hl : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hmeas : AEStronglyMeasurable (fun s : ℝ => paperFT w s * (Real.log (|s| / (2 * π)) : ℂ)) :=
    ((continuous_paperFT_ofReal' hw hsupp).measurable.mul (Complex.measurable_ofReal.comp
      (Real.measurable_log.comp (measurable_id.abs.div_const _)))).aestronglyMeasurable
  refine integrable_of_log_near_zero hmeas (A := C) (B₁ := C * Real.log (2 * π))
    (B₂ := C * (2 * (2 + Real.log (2 * π)))) (by positivity) (fun s _ => ?_) (fun s hs => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖paperFT w s‖ ≤ C := by
      refine (hC s).1.trans ?_
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg s]
    have h2 := abs_log_abs_div_two_pi_le s
    calc ‖paperFT w s‖ * |Real.log (|s| / (2 * π))| ≤ C * (|Real.log s| + Real.log (2 * π)) :=
          mul_le_mul h1 h2 (abs_nonneg _) hC0
      _ = _ := by ring
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := abs_log_abs_div_two_pi_le s
    have hlog : |Real.log s| ≤ 2 * Real.sqrt |s| := by
      rw [← Real.log_abs, abs_of_nonneg (Real.log_nonneg hs)]
      have := Real.log_le_rpow_div (abs_nonneg s) (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [Real.sqrt_eq_rpow]; linarith
    have hk := sqrt_add_div_le_rpow (abs_nonneg s) hl
    rw [sq_abs] at hk
    calc ‖paperFT w s‖ * |Real.log (|s| / (2 * π))|
        ≤ C / (1 + s ^ 2) * (2 * Real.sqrt |s| + Real.log (2 * π)) :=
          mul_le_mul (hC s).1 (by linarith) (abs_nonneg _) (by positivity)
      _ = C * ((2 * Real.sqrt |s| + Real.log (2 * π)) / (1 + s ^ 2)) := by ring
      _ ≤ C * (2 * (2 + Real.log (2 * π)) * (1 + |s|) ^ (-(3 / 2 : ℝ))) := by
          rw [abs_abs] at hk; gcongr
      _ = _ := by ring

/-- The constant `c_w = (1/2π) ∫ ŵ(s) log(|s|/2π) ds` of the smoothed zero count. -/
def zeroCountConst (w : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ s : ℝ, paperFT w s * (Real.log (|s| / (2 * π)) : ℂ)

/-- **The Gamma term of the dilated test**: `∫ ŵ(τ/T) μ(τ) dτ = T w(0) log T + c_w T + E` with
`|E| ≤ C ‖muRem‖₁`, where `C` bounds `ŵ` on the real axis. -/
theorem exists_gammaTerm_dilation (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ∃ K : ℝ, ∀ T : ℝ, 0 < T →
      ‖(∫ τ : ℝ, paperFT w ((τ / T : ℝ) : ℂ) * (mu τ : ℂ)) -
        ((T : ℂ) * w 0 * (Real.log T : ℂ) + (T : ℂ) * zeroCountConst w)‖ ≤ K := by
  obtain ⟨C, hC0, hC⟩ := exists_paperFT_decay hw hsupp
  have hCb : ∀ s : ℝ, ‖paperFT w s‖ ≤ C := fun s => (hC s).1.trans (by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg s])
  refine ⟨C * ∫ τ, |muRem τ|, fun T hT => ?_⟩
  have hWc := continuous_paperFT_ofReal' hw hsupp
  have hWi := integrable_paperFT_ofReal' hw hsupp
  have hGi := integrable_paperFT_mul_log hw hsupp
  have hTinv : T⁻¹ ≠ 0 := inv_ne_zero hT.ne'
  -- the three pieces as functions of `τ`
  set W : ℝ → ℂ := fun τ => paperFT w ((τ / T : ℝ) : ℂ) with hW
  have hWT : Integrable W := by
    have := hWi.comp_mul_left' hTinv
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hW, div_eq_inv_mul]
  have hGT : Integrable (fun τ : ℝ => paperFT w ((T⁻¹ * τ : ℝ) : ℂ) *
      (Real.log (|T⁻¹ * τ| / (2 * π)) : ℂ)) := hGi.comp_mul_left' hTinv
  have hRT : Integrable (fun τ : ℝ => W τ * (muRem τ : ℂ)) := by
    refine (integrable_muRem.norm.const_mul C).mono'
      ((hWc.comp (continuous_id.div_const T)).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable integrable_muRem.aestronglyMeasurable))
      (Filter.Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hCb _) (norm_nonneg _)
  -- pointwise split off `τ = 0`
  have hae : (fun τ : ℝ => paperFT w ((τ / T : ℝ) : ℂ) * (mu τ : ℂ)) =ᵐ[volume]
      fun τ => ((1 / (2 * π) * Real.log T : ℝ) : ℂ) * W τ +
        ((1 / (2 * π) : ℝ) : ℂ) * (paperFT w ((T⁻¹ * τ : ℝ) : ℂ) *
          (Real.log (|T⁻¹ * τ| / (2 * π)) : ℂ)) + W τ * (muRem τ : ℂ) := by
    have h0 : ∀ᵐ τ : ℝ, τ ≠ 0 := by
      have := (measure_eq_zero_iff_ae_notMem (μ := volume) (s := ({0} : Set ℝ))).1
        (measure_singleton 0)
      exact this.mono fun τ h => by simpa using h
    refine h0.mono fun τ hτ => ?_
    have hlog : Real.log (|τ| / (2 * π)) = Real.log T + Real.log (|T⁻¹ * τ| / (2 * π)) := by
      rw [← Real.log_mul hT.ne' (by positivity)]
      congr 1
      rw [abs_mul, abs_inv, abs_of_pos hT]; field_simp
    have hmu : mu τ = 1 / (2 * π) * Real.log (|τ| / (2 * π)) + muRem τ := by
      rw [muRem]; ring
    simp only [hW, ← div_eq_inv_mul]
    rw [hmu, hlog]
    push_cast; ring_nf
  rw [integral_congr_ae hae, integral_add (by
      exact (hWT.const_mul _).add (hGT.const_mul _)) hRT,
    integral_add (hWT.const_mul _) (hGT.const_mul _), integral_const_mul, integral_const_mul]
  -- rescale the first two integrals
  have hW1 : ∫ τ, W τ = (T : ℂ) * (2 * π * w 0) := by
    have := Measure.integral_comp_mul_left (fun s : ℝ => paperFT w s) T⁻¹
    rw [inv_inv, abs_of_pos hT, integral_paperFT_ofReal hw hsupp, Complex.real_smul] at this
    rw [← this]
    congr 1; funext τ; simp only [hW, div_eq_inv_mul]
  have hG1 : (∫ τ : ℝ, paperFT w ((T⁻¹ * τ : ℝ) : ℂ) * (Real.log (|T⁻¹ * τ| / (2 * π)) : ℂ)) =
      (T : ℂ) * ∫ s : ℝ, paperFT w s * (Real.log (|s| / (2 * π)) : ℂ) := by
    have := Measure.integral_comp_mul_left
      (fun s : ℝ => paperFT w s * (Real.log (|s| / (2 * π)) : ℂ)) T⁻¹
    rw [inv_inv, abs_of_pos hT, Complex.real_smul] at this
    exact this
  rw [hW1, hG1]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hmain : ((1 / (2 * π) * Real.log T : ℝ) : ℂ) * ((T : ℂ) * (2 * π * w 0)) +
      ((1 / (2 * π) : ℝ) : ℂ) * ((T : ℂ) * ∫ s : ℝ, paperFT w s * (Real.log (|s| / (2 * π)) : ℂ)) =
      (T : ℂ) * w 0 * (Real.log T : ℂ) + (T : ℂ) * zeroCountConst w := by
    rw [zeroCountConst]; push_cast; field_simp
  rw [hmain, add_sub_cancel_left]
  calc ‖∫ τ, W τ * (muRem τ : ℂ)‖ ≤ ∫ τ, ‖W τ * (muRem τ : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ, C * |muRem τ| := by
        refine integral_mono hRT.norm (integrable_muRem.norm.const_mul C) fun τ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hCb _) (abs_nonneg _)
    _ = C * ∫ τ, |muRem τ| := integral_const_mul _ _

/-- The dilated test `T w(Tu)` has transform `ŵ(z/T)`. -/
lemma paperFT_landauTest_zero {T : ℝ} (hT : 0 < T) (z : ℂ) :
    paperFT (landauTest w T 0) z = paperFT w (z / T) := by
  rw [paperFT_landauTest w hT 0 z]; simp

/-- **Smoothed Riemann–von Mangoldt formula.**  For a `C²` profile `w` supported in `[−1, 1]` there is
`K` with `|Σ_ρ m_ρ ŵ(γ_ρ/T) − (T w(0) log T + c_w T)| ≤ K` for all `T ≥ 2`, the sum over all
nontrivial zeros with multiplicity. -/
theorem exists_smoothedZeroCount (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ∃ K : ℝ, ∀ T : ℝ, 2 ≤ T →
      ‖(∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT w (gammaOf ρ / T)) -
        ((T : ℂ) * w 0 * (Real.log T : ℂ) + (T : ℂ) * zeroCountConst w)‖ ≤ K := by
  obtain ⟨K, hK⟩ := exists_gammaTerm_dilation hw hsupp
  refine ⟨2 * Real.exp (1 / 2) * (∫ u, ‖w u‖) + K, fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  have hwi := (integrable_and_smul hw hsupp).1
  obtain ⟨hkd, hkc⟩ := landauTest_contDiff_hasCompactSupport hw hsupp hTpos 0
  have hEF := (Zeta23.WeilEF.EF_lit_zetaZeroConfig _ hkd hkc).2
  have hzs : (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
      paperFT w (gammaOf ρ / T)) = ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
      paperFT (landauTest w T 0) (gammaOf ρ) := by
    congr 1; funext ρ; rw [paperFT_landauTest_zero hTpos]
  -- the prime side is empty: `T log n > 1` for `n ≥ 2`, and `Λ(0) = Λ(1) = 0`
  have hprime : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (landauTest w T 0 (Real.log n) + landauTest w T 0 (-Real.log n))) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hlog : 1 < T * Real.log n := by
        have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
        have := Real.log_two_gt_d9
        nlinarith
      have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have h1 : 1 < |T * (Real.log n - 0)| := by
        rw [sub_zero, abs_mul, abs_of_pos hTpos, abs_of_nonneg hlog0]; exact hlog
      have h2 : 1 < |T * (-Real.log n - 0)| := by
        rw [sub_zero, abs_mul, abs_of_pos hTpos, abs_neg, abs_of_nonneg hlog0]; exact hlog
      rw [landauTest_eq_zero hsupp h1, landauTest_eq_zero hsupp h2, add_zero, mul_zero]
  have hgam : (∫ τ : ℝ, paperFT (landauTest w T 0) τ * (mu τ : ℂ)) =
      ∫ τ : ℝ, paperFT w ((τ / T : ℝ) : ℂ) * (mu τ : ℂ) := by
    congr 1; funext τ; rw [paperFT_landauTest_zero hTpos]; push_cast; rfl
  rw [hzs, hEF, EF.literatureRHS, EF.gamma_term, hprime, hgam]
  have hpole : ∀ s : ℂ, |s.im| ≤ 1 / 2 →
      ‖paperFT (landauTest w T 0) s‖ ≤ Real.exp (1 / 2) * ∫ u, ‖w u‖ := by
    intro s hs
    refine (norm_pole_landauTest_le hwi hsupp hTpos le_rfl s hs).trans ?_
    gcongr
    rw [zero_add, div_le_one hTpos]; linarith
  have hI : |(I / 2 : ℂ).im| ≤ 1 / 2 := by simp [abs_of_pos]
  have hI' : |(-I / 2 : ℂ).im| ≤ 1 / 2 := by norm_num [abs_div]
  have hG := hK T hTpos
  set G := ∫ τ : ℝ, paperFT w ((τ / T : ℝ) : ℂ) * (mu τ : ℂ)
  set M := (T : ℂ) * w 0 * (Real.log T : ℂ) + (T : ℂ) * zeroCountConst w
  calc ‖paperFT (landauTest w T 0) (I / 2) + paperFT (landauTest w T 0) (-I / 2) - 0 + G - M‖
      = ‖paperFT (landauTest w T 0) (I / 2) + paperFT (landauTest w T 0) (-I / 2) + (G - M)‖ := by
        ring_nf
    _ ≤ ‖paperFT (landauTest w T 0) (I / 2)‖ + ‖paperFT (landauTest w T 0) (-I / 2)‖ + ‖G - M‖ :=
        norm_add₃_le
    _ ≤ _ := by linarith [hpole _ hI, hpole _ hI']

end Profile

end RHTower

end
