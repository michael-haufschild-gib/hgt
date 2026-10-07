import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonMode
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The logarithmic boundary singularity of the constructed polar modes -/

noncomputable section

open MeasureTheory Set Complex Filter Topology

namespace RHTower.WeilHigherDenominator

private lemma hasDerivAt_arsinh_div {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.arsinh (u / y))
      (Real.sqrt (t ^ 2 + y ^ 2))⁻¹ t := by
  have hd := (Real.hasDerivAt_arsinh (t / y)).comp t ((hasDerivAt_id t).div_const y)
  have he : 1 + (t / y) ^ 2 = (t ^ 2 + y ^ 2) / y ^ 2 := by
    field_simp
    ring
  have hs : Real.sqrt (1 + (t / y) ^ 2) = Real.sqrt (t ^ 2 + y ^ 2) / y := by
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hy]
  have hv : (Real.sqrt (1 + (t / y) ^ 2))⁻¹ * (1 / y) =
      (Real.sqrt (t ^ 2 + y ^ 2))⁻¹ := by
    rw [hs, inv_div]
    field_simp
  simpa only [hv, Function.comp_def, id_eq] using hd

/-- Exact logarithmic singularity of the constant local boundary weight. -/
theorem integral_inv_sqrt_quadratic {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    (∫ t in a..b, (Real.sqrt (t ^ 2 + y ^ 2))⁻¹) =
      Real.arsinh (b / y) - Real.arsinh (a / y) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_arsinh_div hy t)
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀
  · fun_prop
  · intro t
    exact (Real.sqrt_pos.mpr (by positivity : 0 < t ^ 2 + y ^ 2)).ne'

theorem integral_inv_sqrt_symmetric {y η : ℝ} (hy : 0 < y) (hη : 0 < η) :
    (∫ t in (-η)..η, (Real.sqrt (t ^ 2 + y ^ 2))⁻¹) =
      2 * Real.log (η + Real.sqrt (η ^ 2 + y ^ 2)) - 2 * Real.log y := by
  rw [integral_inv_sqrt_quadratic hy, neg_div, Real.arsinh_neg, sub_neg_eq_add,
    ← two_mul, Real.arsinh]
  have he : 1 + (η / y) ^ 2 = (η ^ 2 + y ^ 2) / y ^ 2 := by field_simp; ring
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hy,
    ← add_div, Real.log_div (by positivity) hy.ne']
  ring

private lemma norm_boundary_point (y t : ℝ) :
    ‖1 + (y : ℂ) * I - (t : ℂ)‖ = Real.sqrt ((t - 1) ^ 2 + y ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp only [normSq_apply, sub_re, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, sub_zero, add_zero, sub_im, add_im, one_im, mul_im,
    mul_one, zero_add]
  ring

private lemma boundary_denom_pos {y : ℝ} (hy : 0 < y) (t : ℝ) :
    0 < ‖1 + (y : ℂ) * I - (t : ℂ)‖ := by
  rw [norm_boundary_point]
  apply Real.sqrt_pos.mpr
  positivity

private lemma boundary_real_le_norm (y t : ℝ) :
    |t - 1| ≤ ‖1 + (y : ℂ) * I - (t : ℂ)‖ := by
  simpa [abs_sub_comm] using abs_re_le_norm (1 + (y : ℂ) * I - (t : ℂ))

/-- The tail has a majorant independent of the height approaching zero. -/
theorem norm_polarKernel_boundary_tail (ρ : ℂ) {y t : ℝ} (hy : 0 < y)
    (ht : t ∉ Icc (1 / 2 : ℝ) (3 / 2)) :
    ‖polarKernel ρ (1 + (y : ℂ) * I) t‖ ≤
      (1 + 2 * ‖I - 1‖) * ‖polarKernel ρ I t‖ := by
  have hsep : 1 / 2 ≤ |t - 1| := by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]; linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ t - 1)]; linarith
  have hi : 0 < ‖I - (t : ℂ)‖ := by
    have h : (1 : ℝ) ≤ ‖I - (t : ℂ)‖ := by
      simpa only [sub_im, I_im, ofReal_im, sub_zero, abs_one] using
        abs_im_le_norm (I - (t : ℂ))
    exact lt_of_lt_of_le zero_lt_one h
  have htri : ‖I - (t : ℂ)‖ ≤ |t - 1| + ‖I - 1‖ := by
    calc
      _ = ‖((1 : ℂ) - t) + (I - 1)‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ) - t‖ + ‖I - 1‖ := norm_add_le _ _
      _ = _ := by rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hb : ‖I - (t : ℂ)‖ ≤ (1 + 2 * ‖I - 1‖) * ‖1 + (y : ℂ) * I - (t : ℂ)‖ := by
    calc
      _ ≤ (1 + 2 * ‖I - 1‖) * |t - 1| := by nlinarith [norm_nonneg (I - 1)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (boundary_real_le_norm y t) (by positivity)
  simp only [polarKernel, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  rw [← mul_div_assoc, div_le_div_iff₀ (boundary_denom_pos hy t) hi]
  calc
    _ ≤ ‖((|t| : ℝ) : ℂ) ^ (-ρ)‖ *
        ((1 + 2 * ‖I - 1‖) * ‖1 + (y : ℂ) * I - (t : ℂ)‖) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

private lemma boundary_weight_lipschitz {ρ : ℂ} (hρ : 0 < ρ.re) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc (1 / 2 : ℝ) (3 / 2),
      ‖(t : ℂ) ^ (-ρ) - 1‖ ≤ L * |t - 1| := by
  have hρ₀ : -ρ ≠ 0 := neg_ne_zero.mpr (by intro h; simp [h] at hρ)
  have hc : ContinuousOn (fun t : ℝ => -ρ * (t : ℂ) ^ (-ρ - 1)) (Icc (1 / 2) (3 / 2)) := by
    intro t ht
    exact (continuousAt_const.mul (continuousAt_ofReal_cpow_const t (-ρ - 1)
      (Or.inr (by linarith [ht.1])))).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (hu : u ∈ Icc (1 / 2 : ℝ) (3 / 2)) =>
      (hasDerivAt_ofReal_cpow_const (by linarith [hu.1]) hρ₀).hasDerivWithinAt)
    (fun u hu => (hC u hu).trans (le_max_left C 0)) (convex_Icc _ _)
    (show (1 : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) from by norm_num) ht
  simpa only [ofReal_one, one_cpow, Real.norm_eq_abs] using h

private def boundaryCutoff (y t : ℝ) : ℂ :=
  (Icc (1 / 2 : ℝ) (3 / 2)).indicator
    (fun u => (‖1 + (y : ℂ) * I - (u : ℂ)‖ : ℂ)⁻¹) t

private lemma integrable_boundaryCutoff {y : ℝ} (hy : 0 < y) :
    Integrable (boundaryCutoff y) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply Continuous.integrableOn_Icc
  apply Continuous.inv₀
  · fun_prop
  · intro t
    exact ofReal_ne_zero.mpr (boundary_denom_pos hy t).ne'

private lemma integral_boundaryCutoff {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ, boundaryCutoff y t) =
      ((2 * Real.log (1 / 2 + Real.sqrt ((1 / 2 : ℝ) ^ 2 + y ^ 2)) -
        2 * Real.log y : ℝ) : ℂ) := by
  unfold boundaryCutoff
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)]
  simp_rw [norm_boundary_point, ← ofReal_inv]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  calc
    _ = ∫ t in (-(1 / 2 : ℝ))..(1 / 2), (Real.sqrt (t ^ 2 + y ^ 2))⁻¹ := by
      have h := intervalIntegral.integral_comp_add_right
        (a := 1 / 2) (b := 3 / 2) (fun t : ℝ => (Real.sqrt (t ^ 2 + y ^ 2))⁻¹) (-1)
      norm_num only [show (1 / 2 + -1 : ℝ) = -(1 / 2) from by norm_num,
        show (3 / 2 + -1 : ℝ) = 1 / 2 from by norm_num] at h
      simpa only [sub_eq_add_neg] using h
    _ = _ := integral_inv_sqrt_symmetric hy (by norm_num)

private lemma boundary_remainder_majorant {ρ : ℂ} (hρ : 0 < ρ.re) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ℝ, 0 < y → ∀ t : ℝ,
      ‖polarKernel ρ (1 + (y : ℂ) * I) t - boundaryCutoff y t‖ ≤
        (Icc (1 / 2 : ℝ) (3 / 2)).indicator (fun _ => L) t +
          (1 + 2 * ‖I - 1‖) * ‖polarKernel ρ I t‖ := by
  obtain ⟨L, hL₀, hL⟩ := boundary_weight_lipschitz hρ
  refine ⟨L, hL₀, fun y hy t => ?_⟩
  by_cases ht : t ∈ Icc (1 / 2 : ℝ) (3 / 2)
  · rw [indicator_of_mem ht]
    have ht₀ : 0 ≤ t := by linarith [ht.1]
    have he : polarKernel ρ (1 + (y : ℂ) * I) t - boundaryCutoff y t =
        ((t : ℂ) ^ (-ρ) - 1) / (‖1 + (y : ℂ) * I - (t : ℂ)‖ : ℂ) := by
      simp only [polarKernel, boundaryCutoff, indicator_of_mem ht, abs_of_nonneg ht₀]
      rw [sub_div, one_div]
    rw [he, norm_div, norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    apply (div_le_iff₀ (boundary_denom_pos hy t)).mpr
    exact (hL t ht).trans (mul_le_mul_of_nonneg_left (boundary_real_le_norm y t) hL₀)
  · simp only [boundaryCutoff, indicator_of_notMem ht, sub_zero, zero_add]
    exact norm_polarKernel_boundary_tail ρ hy ht

/-- Subtracting the explicit logarithm leaves a bounded error for the actual integral. -/
theorem polarKernel_boundary_remainder_bounded {ρ : ℂ}
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(∫ t : ℝ, polarKernel ρ (1 + (y : ℂ) * I) t) + (2 * Real.log y : ℝ)‖ ≤ C := by
  obtain ⟨L, _, hL⟩ := boundary_remainder_majorant hρ₀
  let M : ℝ → ℝ := fun t => (Icc (1 / 2 : ℝ) (3 / 2)).indicator (fun _ => L) t +
    (1 + 2 * ‖I - 1‖) * ‖polarKernel ρ I t‖
  have hM : Integrable M := by
    apply Integrable.add
    · exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
    · exact (integrable_polarKernel_axis hρ₀ hρ₁).norm.const_mul _
  have hc : Continuous (fun y : ℝ =>
      2 * Real.log (1 / 2 + Real.sqrt ((1 / 2 : ℝ) ^ 2 + y ^ 2))) := by
    apply continuous_const.mul
    apply Continuous.log
    · fun_prop
    · intro y
      positivity
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hc.continuousOn
  refine ⟨(∫ t : ℝ, M t) + B, fun y hy hy₁ => ?_⟩
  have hz : 0 < (1 + (y : ℂ) * I).im := by simpa using hy
  have hF := integrable_polarKernel hρ₀ hρ₁ hz
  have hcut := integrable_boundaryCutoff hy
  have hR : ‖∫ t : ℝ, polarKernel ρ (1 + (y : ℂ) * I) t - boundaryCutoff y t‖ ≤
      ∫ t : ℝ, M t := by
    apply (norm_integral_le_integral_norm _).trans
    exact integral_mono_ae (hF.sub hcut).norm hM (Eventually.of_forall (hL y hy))
  have he : (∫ t : ℝ, polarKernel ρ (1 + (y : ℂ) * I) t) + (2 * Real.log y : ℝ) =
      (∫ t : ℝ, polarKernel ρ (1 + (y : ℂ) * I) t - boundaryCutoff y t) +
        ((2 * Real.log (1 / 2 + Real.sqrt ((1 / 2 : ℝ) ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
    rw [integral_sub hF hcut, integral_boundaryCutoff hy, ofReal_sub]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add hR
  simpa only [Complex.norm_real] using hB y ⟨hy.le, hy₁⟩

/-- The leading logarithmic boundary coefficient is derived from the convergent integral. -/
theorem polarKernel_boundary_one {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    Tendsto (fun y : ℝ => (∫ t : ℝ, polarKernel ρ (1 + (y : ℂ) * I) t) /
      (Real.log y : ℂ)) (𝓝[>] 0) (𝓝 (-2)) := by
  obtain ⟨C, hC⟩ := polarKernel_boundary_remainder_bounded hρ₀ hρ₁
  let F : ℝ → ℂ := fun y => ∫ t : ℝ, polarKernel ρ (1 + (y : ℂ) * I) t
  have hypos : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < y := self_mem_nhdsWithin
  have hyone : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  have hinv : Tendsto (fun y : ℝ => |(Real.log y)⁻¹|) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_zero, Function.comp_def] using
      (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero).abs
  have hzero : Tendsto (fun y : ℝ => (F y + (2 * Real.log y : ℝ)) /
      (Real.log y : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun y => |C| * |(Real.log y)⁻¹|)
    · filter_upwards [hypos, hyone] with y hy hy₁
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, abs_inv]
      exact mul_le_mul_of_nonneg_right ((hC y hy hy₁.le).trans (le_abs_self C))
        (inv_nonneg.mpr (abs_nonneg _))
    · simpa only [mul_zero] using tendsto_const_nhds.mul hinv
  have he : (fun y : ℝ => (F y + (2 * Real.log y : ℝ)) / (Real.log y : ℂ) - 2) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => F y / (Real.log y : ℂ)) := by
    filter_upwards [hypos, hyone] with y hy hy₁
    have hlog : (Real.log y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.log_neg hy hy₁).ne
    push_cast
    field_simp
    ring
  simpa only [zero_sub] using (hzero.sub_const (2 : ℂ)).congr' he

theorem polarMode_boundary_one {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    Tendsto (fun y : ℝ => polarMode ρ (1 + (y : ℂ) * I) /
      ((Real.sqrt y : ℂ) * (Real.log y : ℂ))) (𝓝[>] 0) (𝓝 (-2)) := by
  apply (polarKernel_boundary_one hρ₀ hρ₁).congr'
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  have hs : (Real.sqrt y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [polarMode, add_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
    I_re, mul_zero, add_zero, zero_add]
  field_simp

/-- The normalized boundary coefficient is nonzero everywhere in the open strip. -/
theorem normalizedPolarMode_boundary_one {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    Tendsto (fun y : ℝ => normalizedPolarMode ρ (1 + (y : ℂ) * I) /
      ((Real.sqrt y : ℂ) * (Real.log y : ℂ))) (𝓝[>] 0)
        (𝓝 ((-2 : ℂ) / polarAxisFactor ρ)) := by
  convert (polarMode_boundary_one hρ₀ hρ₁).div_const (polarAxisFactor ρ) using 1
  ext y
  simp only [normalizedPolarMode, div_div]
  congr 1
  ring

end RHTower.WeilHigherDenominator
