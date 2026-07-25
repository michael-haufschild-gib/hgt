import GaloisForLFunctions.RHTower.SmoothAFEZetaDualReflection

/-!
# Uniform right-half-strip bound for the zeta functional-equation factor

The quantitative digamma estimate in `RouteBChiDecay` implies
`‖χ(σ+it)‖ ≤ 1` uniformly for `1/2 ≤ σ < 1` once `|t| ≥ 256`.
The deliberately coarse threshold keeps later Gaussian contour estimates
elementary.
-/

noncomputable section

namespace RHTower

open Complex

theorem zetaChi_large_height_condition {t : ℝ} (ht : 256 ≤ t) :
    Real.log Real.pi +
        (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) <
      Real.log (t / 2) := by
  have ht0 : 0 < t := by linarith
  have htHalf : 1 ≤ t / 2 := by linarith
  have hfirst : 1 / (t / 2) ^ 2 ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith
  have hsecond : Real.pi / (2 * (t / 2)) < 1 := by
    rw [show 2 * (t / 2) = t by ring, div_lt_one ht0]
    linarith [Real.pi_lt_four]
  have herror :
      1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2)) < 2 := by
    linarith
  have hexpTwo : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by ring, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hratioPos : 0 < t / (2 * Real.pi) := by positivity
  have hratio : 9 < t / (2 * Real.pi) := by
    rw [lt_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_lt_four]
  have hlogRatio : 2 < Real.log (t / (2 * Real.pi)) :=
    (Real.lt_log_iff_exp_lt hratioPos).2 (hexpTwo.trans hratio)
  have hlog :
      Real.log (t / 2) - Real.log Real.pi =
        Real.log (t / (2 * Real.pi)) := by
    rw [← Real.log_div (div_ne_zero ht0.ne' (by norm_num))
      Real.pi_ne_zero]
    congr 1
    field_simp [Real.pi_ne_zero]
  rw [← sub_pos] at *
  rw [show Real.log (t / 2) -
      (Real.log Real.pi +
        (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2)))) =
      (Real.log (t / 2) - Real.log Real.pi) -
        (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) by ring,
    hlog]
  linarith

/-- Uniform large-height decay on the right half of the critical strip. -/
theorem norm_zetaChi_le_one_right_half_strip
    {σ t : ℝ} (hσlow : 1 / 2 ≤ σ) (hσhigh : σ < 1)
    (ht : 256 ≤ |t|) :
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 1 := by
  rw [norm_zetaChi_real_add_im_eq_abs σ t]
  rcases eq_or_lt_of_le hσlow with rfl | hσ
  · exact (by simpa [linePt] using (norm_zetaChi_line |t|).le)
  · exact (norm_zetaChi_lt_one hσ hσhigh
      (by linarith [abs_nonneg t])
      (zetaChi_large_height_condition ht)).le

end RHTower
