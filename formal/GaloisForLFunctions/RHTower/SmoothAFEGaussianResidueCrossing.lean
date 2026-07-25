import GaloisForLFunctions.RHTower.SmoothAFEGaussianReciprocalContour
import GaloisForLFunctions.RHTower.SmoothAFEGaussianContour

/-!
# Residue crossing for the Gaussian Mellin cutoff

This module completes the contour geometry of the Gaussian smooth cutoff.  For `x > 0`, it shifts
the full integrand `x⁻ʷ exp(w²) / w` from a positive vertical line to a negative vertical line.
The proof:

1. bounds both horizontal sides uniformly by a Gaussian;
2. decomposes the integrand into `1 / w` plus an entire divided difference;
3. applies the rectangle theorem to the entire part;
4. evaluates the limiting reciprocal contour explicitly.

The resulting inverse-Mellin cutoff changes by exactly one when the contour crosses zero, matching
the unit residue of the kernel.  No asymptotic or zeta-function hypothesis is used.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set Filter Topology

theorem norm_smoothAFEMellinIntegrand_horizontal_crossing_le
    {x B u t : ℝ} (hx : 0 < x) (hu : |u| ≤ B) (ht : 1 ≤ |t|) :
    ‖smoothAFEMellinIntegrand x ((u : ℂ) + (t : ℂ) * I)‖
      ≤ (Real.exp (|Real.log x| * B) * Real.exp (B ^ 2)) *
          Real.exp (-(t ^ 2)) := by
  have hxpow : x ^ (-u) ≤ Real.exp (|Real.log x| * B) := by
    rw [Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.2
    calc
      Real.log x * -u ≤ |Real.log x * -u| := le_abs_self _
      _ = |Real.log x| * |u| := by rw [abs_mul, abs_neg]
      _ ≤ |Real.log x| * B :=
        mul_le_mul_of_nonneg_left hu (abs_nonneg _)
  have hu_sq : u ^ 2 ≤ B ^ 2 := by
    nlinarith [sq_nonneg (B - u), sq_nonneg (B + u),
      (abs_le.mp hu).1, (abs_le.mp hu).2]
  have hre :
      ((((u : ℂ) + (t : ℂ) * I) ^ 2).re) = u ^ 2 - t ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hden : 1 ≤ ‖(u : ℂ) + (t : ℂ) * I‖ := by
    calc
      1 ≤ |t| := ht
      _ = |(((u : ℂ) + (t : ℂ) * I)).im| := by simp
      _ ≤ ‖(u : ℂ) + (t : ℂ) * I‖ := Complex.abs_im_le_norm _
  rw [smoothAFEMellinIntegrand, smoothAFEGaussianKernel, norm_mul, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp, hre]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  calc
    x ^ (-u) * (Real.exp (u ^ 2 - t ^ 2) /
        ‖(u : ℂ) + (t : ℂ) * I‖)
      ≤ x ^ (-u) * Real.exp (u ^ 2 - t ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (div_le_iff₀ (zero_lt_one.trans_le hden)).2
        exact le_mul_of_one_le_right (Real.exp_nonneg _) hden
    _ ≤ Real.exp (|Real.log x| * B) * Real.exp (B ^ 2 - t ^ 2) := by
      gcongr
    _ = (Real.exp (|Real.log x| * B) * Real.exp (B ^ 2)) *
          Real.exp (-(t ^ 2)) := by
      rw [show B ^ 2 - t ^ 2 = B ^ 2 + (-(t ^ 2)) by ring, Real.exp_add]
      ring

theorem tendsto_smoothAFEMellinIntegrand_horizontal
    {x a b : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ =>
      ∫ u : ℝ in a..b, smoothAFEMellinIntegrand x ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ := |a| + |b|
  let C : ℝ := Real.exp (|Real.log x| * B) * Real.exp (B ^ 2)
  have hB : 0 ≤ B := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hexp0 : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Filter.tendsto_neg_atTop_atBot.comp
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hmajor : Tendsto (fun T : ℝ => C * |b - a| * Real.exp (-(T ^ 2)))
      atTop (𝓝 0) := by
    simpa using hexp0.const_mul (C * |b - a|)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hbd : ∀ u ∈ Set.uIoc a b,
      ‖smoothAFEMellinIntegrand x ((u : ℂ) + (T : ℂ) * I)‖
        ≤ C * Real.exp (-(T ^ 2)) := by
    intro u hu
    have hu' : min a b ≤ u ∧ u ≤ max a b := by
      change u ∈ Set.uIcc a b
      exact Set.uIoc_subset_uIcc hu
    have hua : -B ≤ u := by
      dsimp [B]
      calc
        -(|a| + |b|) ≤ min a b := by
          apply le_min
          · linarith [neg_abs_le a, abs_nonneg b]
          · linarith [neg_abs_le b, abs_nonneg a]
        _ ≤ u := hu'.1
    have hub : u ≤ B := by
      dsimp [B]
      calc
        u ≤ max a b := hu'.2
        _ ≤ |a| + |b| := by
          apply max_le
          · linarith [le_abs_self a, abs_nonneg b]
          · linarith [le_abs_self b, abs_nonneg a]
    exact norm_smoothAFEMellinIntegrand_horizontal_crossing_le hx
      (abs_le.mpr ⟨hua, hub⟩)
      (by simpa [abs_of_nonneg (zero_le_one.trans hT)] using hT)
  calc
    ‖∫ u : ℝ in a..b, smoothAFEMellinIntegrand x ((u : ℂ) + (T : ℂ) * I)‖
        ≤ (C * Real.exp (-(T ^ 2))) * |b - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = C * |b - a| * Real.exp (-(T ^ 2)) := by ring

theorem tendsto_smoothAFEMellinIntegrand_horizontal_neg
    {x a b : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ =>
      ∫ u : ℝ in a..b, smoothAFEMellinIntegrand x ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
  let B : ℝ := |a| + |b|
  let C : ℝ := Real.exp (|Real.log x| * B) * Real.exp (B ^ 2)
  have hexp0 : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Filter.tendsto_neg_atTop_atBot.comp
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hmajor : Tendsto (fun T : ℝ => C * |b - a| * Real.exp (-(T ^ 2)))
      atTop (𝓝 0) := by
    simpa using hexp0.const_mul (C * |b - a|)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hbd : ∀ u ∈ Set.uIoc a b,
      ‖smoothAFEMellinIntegrand x ((u : ℂ) - (T : ℂ) * I)‖
        ≤ C * Real.exp (-(T ^ 2)) := by
    intro u hu
    have hu' : min a b ≤ u ∧ u ≤ max a b := by
      change u ∈ Set.uIcc a b
      exact Set.uIoc_subset_uIcc hu
    have hua : -B ≤ u := by
      dsimp [B]
      calc
        -(|a| + |b|) ≤ min a b := by
          apply le_min
          · linarith [neg_abs_le a, abs_nonneg b]
          · linarith [neg_abs_le b, abs_nonneg a]
        _ ≤ u := hu'.1
    have hub : u ≤ B := by
      dsimp [B]
      calc
        u ≤ max a b := hu'.2
        _ ≤ |a| + |b| := by
          apply max_le
          · linarith [le_abs_self a, abs_nonneg b]
          · linarith [le_abs_self b, abs_nonneg a]
    have h := norm_smoothAFEMellinIntegrand_horizontal_crossing_le hx
      (abs_le.mpr ⟨hua, hub⟩)
      (show 1 ≤ |-T| by simpa [abs_of_nonneg (zero_le_one.trans hT)] using hT)
    simpa [sub_eq_add_neg, ofReal_neg] using h
  calc
    ‖∫ u : ℝ in a..b, smoothAFEMellinIntegrand x ((u : ℂ) - (T : ℂ) * I)‖
        ≤ (C * Real.exp (-(T ^ 2))) * |b - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = C * |b - a| * Real.exp (-(T ^ 2)) := by ring

theorem integral_smoothAFEMellinIntegrand_residue_crossing
    {x a b : ℝ} (hx : 0 < x) (ha : a < 0) (hb : 0 < b) :
    (∫ t : ℝ, smoothAFEMellinIntegrand x ((b : ℂ) + (t : ℂ) * I))
      - (∫ t : ℝ, smoothAFEMellinIntegrand x ((a : ℂ) + (t : ℂ) * I))
      = 2 * Real.pi := by
  let F : ℂ → ℂ := smoothAFEMellinIntegrand x
  let R : ℂ → ℂ := smoothAFERegularPart x
  let J : ℂ → ℂ := fun z => z⁻¹
  have hRdiff : Differentiable ℂ R := differentiable_smoothAFERegularPart hx
  have hboundary : ∀ T : ℝ, 1 ≤ T →
      (∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I))
        - (∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I))
        + I • (∫ t : ℝ in (-T)..T, F ((b : ℂ) + (t : ℂ) * I))
        - I • (∫ t : ℝ in (-T)..T, F ((a : ℂ) + (t : ℂ) * I))
      =
      (∫ u : ℝ in a..b, J ((u : ℂ) - (T : ℂ) * I))
        - (∫ u : ℝ in a..b, J ((u : ℂ) + (T : ℂ) * I))
        + I • (∫ t : ℝ in (-T)..T, J ((b : ℂ) + (t : ℂ) * I))
        - I • (∫ t : ℝ in (-T)..T, J ((a : ℂ) + (t : ℂ) * I)) := by
    intro T hT
    have hT0 : T ≠ 0 := (zero_lt_one.trans_le hT).ne'
    have hRrect :
        (∫ u : ℝ in a..b, R ((u : ℂ) - (T : ℂ) * I))
          - (∫ u : ℝ in a..b, R ((u : ℂ) + (T : ℂ) * I))
          + I • (∫ t : ℝ in (-T)..T, R ((b : ℂ) + (t : ℂ) * I))
          - I • (∫ t : ℝ in (-T)..T, R ((a : ℂ) + (t : ℂ) * I)) = 0 := by
      have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn R
        ((a : ℂ) - (T : ℂ) * I) ((b : ℂ) + (T : ℂ) * I)
        hRdiff.differentiableOn
      simpa using h
    have hbot : (∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I))
        = (∫ u : ℝ in a..b, J ((u : ℂ) - (T : ℂ) * I))
          + ∫ u : ℝ in a..b, R ((u : ℂ) - (T : ℂ) * I) := by
      rw [← intervalIntegral.integral_add]
      · apply intervalIntegral.integral_congr
        intro u _
        dsimp [F, J, R]
        exact smoothAFEMellinIntegrand_eq_inv_add_regularPart x (by
          intro hzero
          have him := congrArg Complex.im hzero
          simp [hT0] at him)
      · simpa [J] using ((by fun_prop : Continuous fun u : ℝ =>
          (u : ℂ) - (T : ℂ) * I).inv₀ (fun u hzero => by
            have him := congrArg Complex.im hzero
            simp [hT0] at him)).intervalIntegrable a b
      · exact (hRdiff.continuous.comp (by fun_prop)).intervalIntegrable _ _
    have htop : (∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I))
        = (∫ u : ℝ in a..b, J ((u : ℂ) + (T : ℂ) * I))
          + ∫ u : ℝ in a..b, R ((u : ℂ) + (T : ℂ) * I) := by
      rw [← intervalIntegral.integral_add]
      · apply intervalIntegral.integral_congr
        intro u _
        dsimp [F, J, R]
        exact smoothAFEMellinIntegrand_eq_inv_add_regularPart x (by
          intro hzero
          have him := congrArg Complex.im hzero
          simp [hT0] at him)
      · simpa [J] using ((by fun_prop : Continuous fun u : ℝ =>
          (u : ℂ) + (T : ℂ) * I).inv₀ (fun u hzero => by
            have him := congrArg Complex.im hzero
            simp [hT0] at him)).intervalIntegrable a b
      · exact (hRdiff.continuous.comp (by fun_prop)).intervalIntegrable _ _
    have hright : (∫ t : ℝ in (-T)..T, F ((b : ℂ) + (t : ℂ) * I))
        = (∫ t : ℝ in (-T)..T, J ((b : ℂ) + (t : ℂ) * I))
          + ∫ t : ℝ in (-T)..T, R ((b : ℂ) + (t : ℂ) * I) := by
      rw [← intervalIntegral.integral_add]
      · apply intervalIntegral.integral_congr
        intro t _
        dsimp [F, J, R]
        exact smoothAFEMellinIntegrand_eq_inv_add_regularPart x (by
          intro hzero
          have hre := congrArg Complex.re hzero
          have : b = 0 := by simpa using hre
          exact hb.ne' this)
      · simpa [J] using ((by fun_prop : Continuous fun t : ℝ =>
          (b : ℂ) + (t : ℂ) * I).inv₀ (fun t hzero => by
            have hre := congrArg Complex.re hzero
            have : b = 0 := by simpa using hre
            exact hb.ne' this)).intervalIntegrable (-T) T
      · exact (hRdiff.continuous.comp (by fun_prop)).intervalIntegrable _ _
    have hleft : (∫ t : ℝ in (-T)..T, F ((a : ℂ) + (t : ℂ) * I))
        = (∫ t : ℝ in (-T)..T, J ((a : ℂ) + (t : ℂ) * I))
          + ∫ t : ℝ in (-T)..T, R ((a : ℂ) + (t : ℂ) * I) := by
      rw [← intervalIntegral.integral_add]
      · apply intervalIntegral.integral_congr
        intro t _
        dsimp [F, J, R]
        exact smoothAFEMellinIntegrand_eq_inv_add_regularPart x (by
          intro hzero
          have hre := congrArg Complex.re hzero
          have : a = 0 := by simpa using hre
          exact ha.ne this)
      · simpa [J] using ((by fun_prop : Continuous fun t : ℝ =>
          (a : ℂ) + (t : ℂ) * I).inv₀ (fun t hzero => by
            have hre := congrArg Complex.re hzero
            have : a = 0 := by simpa using hre
            exact ha.ne this)).intervalIntegrable (-T) T
      · exact (hRdiff.continuous.comp (by fun_prop)).intervalIntegrable _ _
    rw [hbot, htop, hright, hleft]
    rw [smul_add, smul_add]
    rw [smul_eq_mul] at hRrect ⊢
    linear_combination hRrect
  have hbotF := tendsto_smoothAFEMellinIntegrand_horizontal_neg
    (x := x) (a := a) (b := b) hx
  have htopF := tendsto_smoothAFEMellinIntegrand_horizontal
    (x := x) (a := a) (b := b) hx
  have hrightF : Tendsto (fun T : ℝ =>
      ∫ t : ℝ in (-T)..T, F ((b : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral
      (smoothAFEMellinIntegrand_verticalIntegrable_of_ne hx hb.ne')
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hleftF : Tendsto (fun T : ℝ =>
      ∫ t : ℝ in (-T)..T, F ((a : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral
      (smoothAFEMellinIntegrand_verticalIntegrable_of_ne hx ha.ne)
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hlimF := ((hbotF.sub htopF).add (hrightF.const_smul I)).sub
    (hleftF.const_smul I)
  have hbotJ := tendsto_integral_horizontal_inv_neg a b
  have htopJ := tendsto_integral_horizontal_inv a b
  have hrightJ := tendsto_integral_vertical_inv_of_pos hb
  have hleftJ := tendsto_integral_vertical_inv_of_neg ha
  have hlimJ := ((hbotJ.sub htopJ).add (hrightJ.const_smul I)).sub
    (hleftJ.const_smul I)
  have heq : (I • (∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I))
      - I • (∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * I)))
      = I • ((Real.pi : ℂ)) - I • (-(Real.pi : ℂ)) := by
    have hlimJ' := hlimJ.congr' (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      exact (hboundary T hT).symm)
    have huniq := tendsto_nhds_unique hlimF hlimJ'
    simpa using huniq
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at heq
  have hi : I ≠ 0 := Complex.I_ne_zero
  have hcancel :
      (∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I))
        - (∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * I))
      = (Real.pi : ℂ) - (-(Real.pi : ℂ)) := by
    apply (mul_left_cancel₀ hi)
    simpa [mul_sub, mul_add] using heq
  simpa [F, two_mul] using hcancel

theorem smoothAFECutoffAt_sub_eq_one
    {x a b : ℝ} (hx : 0 < x) (ha : a < 0) (hb : 0 < b) :
    smoothAFECutoffAt b x - smoothAFECutoffAt a x = 1 := by
  unfold smoothAFECutoffAt mellinInv
  rw [Complex.real_smul, Complex.real_smul]
  rw [← mul_sub]
  simp only [smul_eq_mul]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ((∫ t : ℝ, smoothAFEMellinIntegrand x ((b : ℂ) + (t : ℂ) * I))
      - ∫ t : ℝ, smoothAFEMellinIntegrand x ((a : ℂ) + (t : ℂ) * I)) = 1
  rw [integral_smoothAFEMellinIntegrand_residue_crossing hx ha hb]
  norm_cast
  field_simp [Real.pi_ne_zero]

theorem smoothAFECutoffAt_eq_smoothAFECutoff_sub_one
    {x σ : ℝ} (hx : 0 < x) (hσ : σ < 0) :
    smoothAFECutoffAt σ x = smoothAFECutoff x - 1 := by
  have h := smoothAFECutoffAt_sub_eq_one hx hσ zero_lt_one
  unfold smoothAFECutoff
  linear_combination -h

end RHTower
