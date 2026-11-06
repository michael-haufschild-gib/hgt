import Mathlib

/-!
# Positive real parts of shifted quadratic products

Normalizing each factor separates its size from its phase. A finite integral
comparison bounds the total phase displacement on a strip beyond height one half.
-/

open Complex Finset Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

noncomputable section

/-- A right-half-plane factor moves its unit direction by at most its slope. -/
theorem norm_normalized_sub_one_le {w : ℂ} (hw : 0 < w.re) :
    ‖w / (‖w‖ : ℂ) - 1‖ ≤ |w.im| / w.re := by
  have hn : 0 < ‖w‖ := hw.trans_le (Complex.re_le_norm w)
  have hnc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : w.im ^ 2 = ‖w‖ ^ 2 - w.re ^ 2 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith only [h]
  have hs : ‖w - (‖w‖ : ℂ)‖ ^ 2 = (w.re - ‖w‖) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero]
    ring
  have hid : (|w.im| * ‖w‖) ^ 2 - (‖w - (‖w‖ : ℂ)‖ * w.re) ^ 2 =
      ‖w‖ * (‖w‖ - w.re) ^ 2 * (‖w‖ + 2 * w.re) := by
    rw [mul_pow, mul_pow, sq_abs, hs, he]
    ring
  have hsq : (‖w - (‖w‖ : ℂ)‖ * w.re) ^ 2 ≤ (|w.im| * ‖w‖) ^ 2 := by
    have hp : 0 ≤ ‖w‖ * (‖w‖ - w.re) ^ 2 * (‖w‖ + 2 * w.re) := by positivity
    linarith only [hid, hp]
  rw [div_sub_one hnc, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
    div_le_div_iff₀ hn hw]
  nlinarith only [hsq, mul_nonneg (norm_nonneg (w - (‖w‖ : ℂ))) hw.le,
    mul_nonneg (abs_nonneg w.im) hn.le]

/-- Unit factors accumulate chord distance at most additively. -/
theorem norm_unit_product_sub_one_le (u : ℕ → ℂ) (hu : ∀ k, ‖u k‖ = 1) (j : ℕ) :
    ‖(∏ k ∈ range j, u k) - 1‖ ≤ ∑ k ∈ range j, ‖u k - 1‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, sum_range_succ]
    calc
      ‖(∏ k ∈ range j, u k) * u j - 1‖ =
          ‖((∏ k ∈ range j, u k) - 1) * u j + (u j - 1)‖ := by
        congr 1
        ring
      _ ≤ ‖((∏ k ∈ range j, u k) - 1) * u j‖ + ‖u j - 1‖ := norm_add_le _ _
      _ = ‖(∏ k ∈ range j, u k) - 1‖ + ‖u j - 1‖ := by rw [norm_mul, hu, mul_one]
      _ ≤ _ := by linarith only [ih]

/-- A total slope of at most `7/5` keeps the product in a fixed right sector. -/
theorem re_product_ge_norm_div_fifty (v : ℕ → ℂ) (hv : ∀ k, 0 < (v k).re) (j : ℕ)
    (hs : (∑ k ∈ range j, |(v k).im| / (v k).re) ≤ 7 / 5) :
    ‖∏ k ∈ range j, v k‖ / 50 ≤ (∏ k ∈ range j, v k).re := by
  let u : ℕ → ℂ := fun k => v k / (‖v k‖ : ℂ)
  have hn (k : ℕ) : 0 < ‖v k‖ := (hv k).trans_le (Complex.re_le_norm _)
  have hu (k : ℕ) : ‖u k‖ = 1 := by
    simp only [u, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hn k)]
    exact div_self (hn k).ne'
  have hd : ‖(∏ k ∈ range j, u k) - 1‖ ≤ 7 / 5 :=
    (norm_unit_product_sub_one_le u hu j).trans
      ((sum_le_sum fun k _ => norm_normalized_sub_one_le (hv k)).trans hs)
  have hU : ‖∏ k ∈ range j, u k‖ = 1 := by rw [norm_prod]; simp only [hu, prod_const_one]
  have hchord : ‖(∏ k ∈ range j, u k) - 1‖ ^ 2 =
      2 - 2 * (∏ k ∈ range j, u k).re := by
    have h := Complex.sq_norm (∏ k ∈ range j, u k)
    rw [hU, Complex.normSq_apply] at h
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith only [h]
  have hRe : 1 / 50 ≤ (∏ k ∈ range j, u k).re := by
    nlinarith only [hchord, sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 5) |>.mpr hd]
  have hprod : (∏ k ∈ range j, u k) =
      (∏ k ∈ range j, v k) / (‖∏ k ∈ range j, v k‖ : ℂ) := by
    simp only [u, prod_div_distrib, norm_prod, Complex.ofReal_prod]
  have hpn : 0 < ‖∏ k ∈ range j, v k‖ := by
    rw [norm_prod]
    exact prod_pos (fun k _ => hn k)
  rw [hprod, Complex.div_ofReal_re, le_div_iff₀ hpn] at hRe
  linarith only [hRe]

/-- The reciprocal-square sum retains three quarters of its first term. -/
theorem quarter_shift_reciprocal_sum_le {d : ℝ} (hd : 0 < d) (j : ℕ) :
    (∑ k ∈ range j, (((k : ℝ) + 1 / 4) ^ 2 + d ^ 2 / 4)⁻¹) ≤
      (3 / 4) * ((1 / 4 : ℝ) ^ 2 + d ^ 2 / 4)⁻¹ + Real.pi / d := by
  let f : ℝ → ℝ := fun t => (t ^ 2 + d ^ 2 / 4)⁻¹
  have hc : Continuous f := by
    apply Continuous.inv₀ (by fun_prop)
    intro t
    positivity
  have hanti : AntitoneOn f (Ici 0) := by
    intro a ha b hb hab
    dsimp only [f]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    linarith only [pow_le_pow_left₀ ha hab 2]
  have hInt (T : ℝ) : (∫ t in (0 : ℝ)..T, f t) ≤ Real.pi / d := by
    have he : f = fun t : ℝ => ((d / 2) ^ 2 + t ^ 2)⁻¹ := by
      funext t
      dsimp only [f]
      congr 1
      ring
    rw [he, integral_inv_sq_add_sq (by positivity : d / 2 ≠ 0)]
    simp only [zero_div, Real.arctan_zero, sub_zero]
    have h := mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two (T / (d / 2))).le
      (inv_nonneg.mpr (by positivity : 0 ≤ d / 2))
    refine h.trans_eq ?_
    field_simp
  have hlow : f (1 / 4) / 4 ≤ ∫ t in (0 : ℝ)..(1 / 4 : ℝ), f t := by
    have h := integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (continuous_const.intervalIntegrable 0 (1 / 4) :
        IntervalIntegrable (fun _ : ℝ => f (1 / 4)) volume 0 (1 / 4))
      (hc.intervalIntegrable 0 (1 / 4)) (fun t ht => hanti ht.1 (by norm_num) ht.2)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, div_eq_mul_inv,
      one_mul, mul_comm] using h
  cases j with
  | zero => simp only [Finset.range_zero, sum_empty]; positivity
  | succ n =>
    have ha : AntitoneOn f (Icc (1 / 4) (1 / 4 + (n : ℝ))) :=
      hanti.mono (fun t ht => by change 0 ≤ t; linarith [ht.1])
    have hsum := ha.sum_le_integral
    have hadd := integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable 0 (1 / 4))
      (hc.intervalIntegrable (1 / 4) (1 / 4 + (n : ℝ)))
    have hi := hInt (1 / 4 + (n : ℝ))
    change (∑ k ∈ range (n + 1), f ((k : ℝ) + 1 / 4)) ≤ _
    rw [sum_range_succ']
    have he : (∑ k ∈ range n, f (((k + 1 : ℕ) : ℝ) + 1 / 4)) =
        ∑ k ∈ range n, f (1 / 4 + ((k + 1 : ℕ) : ℝ)) := by
      apply sum_congr rfl
      intro k _
      rw [add_comm]
    rw [he]
    change _ ≤ (3 / 4) * f (1 / 4) + Real.pi / d
    linarith only [hsum, hadd, hi, hlow]

/-- Rational constants leave a strict margin beyond strip height one half. -/
theorem quadratic_slope_sum_le {x y : ℝ} (hx : 7 / 5 ≤ x)
    (hy0 : 0 ≤ y) (hy : y ≤ 501 / 1000) (j : ℕ) :
    x * y / 2 *
      (∑ k ∈ range j, (((k : ℝ) + 1 / 4) ^ 2 + (x ^ 2 - y ^ 2) / 4)⁻¹) ≤ 7 / 5 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hysq : y ^ 2 ≤ (501 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hxsq : (7 / 5 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
  have hdiff : 0 < x ^ 2 - y ^ 2 := by nlinarith only [hxsq, hysq]
  let d := Real.sqrt (x ^ 2 - y ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr hdiff
  have hdsq : d ^ 2 = x ^ 2 - y ^ 2 := Real.sq_sqrt hdiff.le
  have hden : 0 < x ^ 2 - y ^ 2 + 1 / 4 := by linarith only [hdiff]
  have hfirst : 3 * x / (2 * (x ^ 2 - y ^ 2 + 1 / 4)) ≤ 13 / 12 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hden)]
    have hm := mul_nonneg hx0.le (sub_nonneg.mpr hx)
    nlinarith only [hm, hysq, hx]
  have hratio : x / d ≤ 43 / 40 := by
    rw [div_le_iff₀ hd]
    have hh : x ^ 2 ≤ (43 / 40 * d) ^ 2 := by
      nlinarith only [hdsq, hysq, hxsq]
    exact (sq_le_sq₀ hx0.le (by positivity)).mp hh
  have hsecond : Real.pi * x / (2 * d) ≤ 2709 / 1600 := by
    calc
      Real.pi * x / (2 * d) = (Real.pi / 2) * (x / d) := by ring
      _ ≤ (63 / 40) * (43 / 40) :=
        mul_le_mul (by linarith only [Real.pi_lt_d2]) hratio
          (div_nonneg hx0.le hd.le) (by norm_num)
      _ = _ := by norm_num
  have hsum := quarter_shift_reciprocal_sum_le hd j
  rw [hdsq] at hsum
  calc
    x * y / 2 * (∑ k ∈ range j,
        (((k : ℝ) + 1 / 4) ^ 2 + (x ^ 2 - y ^ 2) / 4)⁻¹) ≤
        x * y / 2 * ((3 / 4) * ((1 / 4 : ℝ) ^ 2 + (x ^ 2 - y ^ 2) / 4)⁻¹ +
          Real.pi / d) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = y * (3 * x / (2 * (x ^ 2 - y ^ 2 + 1 / 4)) + Real.pi * x / (2 * d)) := by
      have he : (1 / 4 : ℝ) ^ 2 + (x ^ 2 - y ^ 2) / 4 =
          (x ^ 2 - y ^ 2 + 1 / 4) / 4 := by ring
      rw [he]
      field_simp
    _ ≤ y * (13 / 12 + 2709 / 1600) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hy0
    _ ≤ (501 / 1000) * (13 / 12 + 2709 / 1600) :=
      mul_le_mul_of_nonneg_right hy (by norm_num)
    _ ≤ 7 / 5 := by norm_num

/-- Far from the origin, every shifted quadratic product has positive real part. -/
theorem re_shifted_quadratic_product_pos {z : ℂ}
    (hx : 7 / 5 ≤ |z.re|) (hy : |z.im| ≤ 501 / 1000) (j : ℕ) :
    0 < (∏ k ∈ range j, (((k : ℂ) + 1 / 4) ^ 2 + z ^ 2 / 4)).re := by
  let v : ℕ → ℂ := fun k => ((k : ℂ) + 1 / 4) ^ 2 + z ^ 2 / 4
  have hre (k : ℕ) : (v k).re =
      ((k : ℝ) + 1 / 4) ^ 2 + (|z.re| ^ 2 - |z.im| ^ 2) / 4 := by
    simp [v, pow_two, Complex.mul_re]
  have him (k : ℕ) : |(v k).im| = |z.re| * |z.im| / 2 := by
    have he : (v k).im = z.re * z.im / 2 := by
      simp [v, pow_two, Complex.mul_im]
      ring
    rw [he, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hysq := pow_le_pow_left₀ (abs_nonneg z.im) hy 2
  have hxsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 5) hx 2
  have hv (k : ℕ) : 0 < (v k).re := by
    rw [hre]
    nlinarith only [hysq, hxsq, sq_nonneg ((k : ℝ) + 1 / 4)]
  have hs : (∑ k ∈ range j, |(v k).im| / (v k).re) ≤ 7 / 5 := by
    simp_rw [hre, him, div_eq_mul_inv]
    rw [← mul_sum]
    exact quadratic_slope_sum_le hx (abs_nonneg z.im) hy j
  have hp := re_product_ge_norm_div_fifty v hv j hs
  have hn : 0 < ‖∏ k ∈ range j, v k‖ := by
    rw [norm_prod]
    exact prod_pos (fun k _ => (hv k).trans_le (Complex.re_le_norm _))
  exact (div_pos hn (by norm_num)).trans_le hp

end

end GaloisForLFunctions.BiScaleUncertainty.ExactExtremal
