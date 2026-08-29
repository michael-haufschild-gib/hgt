import GaloisForLFunctions.RHTower.Sieve.MixedMomentWindowCompare
import GaloisForLFunctions.RHTower.Sieve.PerronWindowKernel

/-!
# The Perron comparison kernel is dominated by the mixed-moment kernel at every height

`norm_perronCompareKernel_le_windowCompareKernel` compares the two kernels only **above** the
transition height `t₀`, where they visibly agree.  The Perron integral of Lemma 3.1 runs over the
whole range `[-T, T]`, so the comparison is needed below `t₀` as well.

Below `t₀` the third component of `windowCompareKernel` is the constant `4(x+h₁)/t₀`, which is
*smaller* than the analytic kernel's `4(x+h₁)/|t|`; what saves the comparison is that the first two
components already beat it.  Indeed `t₀ ≤ x/h₁` gives `2|t|hh₁/x ≤ 2t₀hh₁/x ≤ 2h`, and the same
hypothesis together with `h ≤ h₁` gives `2t₀hh₁/x ≤ 4(x+h₁)/t₀`.

So under the transition-height hypothesis the analytic kernel is dominated everywhere, and
`integral_mixed_moment_windowCompare_le` can consume the whole Perron integral.
-/

namespace RHTower.Sieve

noncomputable section

/-- **The analytic comparison kernel is dominated by the mixed-moment kernel at every height.** -/
theorem norm_perronCompareKernel_le_windowCompareKernel_all
    {x h h₁ t₀ t : ℝ} (hx : 0 < x) (hh : 0 < h) (hle : h ≤ h₁) (ht₀ : 0 < t₀)
    (hlow : t₀ ≤ x / h₁) (ht : t ≠ 0) :
    ‖perronCompareKernel x h h₁ t‖ ≤ windowCompareKernel x h h₁ t₀ t := by
  have hh₁ : 0 < h₁ := lt_of_lt_of_le hh hle
  have habs : 0 < |t| := abs_pos.mpr ht
  rcases le_or_gt t₀ |t| with hcase | hcase
  · exact norm_perronCompareKernel_le_windowCompareKernel hx hh hh₁ hle ht₀ hcase
  · have hbase := norm_perronCompareKernel_le_min3 hx hh hh₁ hle ht
    have hmax : max |t| t₀ = t₀ := max_eq_right hcase.le
    rw [windowCompareKernel, hmax]
    refine le_min (le_trans hbase (min_le_left _ _)) ?_
    have hbound : t₀ * h₁ ≤ x := by
      rw [le_div_iff₀ hh₁] at hlow
      linarith
    have h2 : 2 * |t| * h * h₁ ≤ 2 * t₀ * h * h₁ := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hcase.le) hh.le) hh₁.le]
    have hstep : 2 * |t| * h * h₁ / x ≤ 2 * t₀ * h * h₁ / x := by
      gcongr
    have h3 : t₀ * h ≤ x := by nlinarith [hbound, ht₀.le, hle]
    have h4 : (t₀ * h₁) * (t₀ * h) ≤ x * x :=
      mul_le_mul hbound h3 (by positivity) hx.le
    have hkey : 2 * t₀ * h * h₁ / x ≤ 4 * (x + h₁) / t₀ := by
      rw [div_le_div_iff₀ hx ht₀]
      nlinarith [h4, hh₁.le, hx.le]
    exact le_trans (le_trans hbase (min_le_left _ _))
      (le_trans (min_le_right _ _) (le_trans hstep hkey))

/-- At the origin both kernels vanish. -/
theorem perronCompareKernel_zero {x h h₁ : ℝ} (hh₁ : h₁ ≠ 0) :
    perronCompareKernel x h h₁ 0 = 0 := by
  have hne : ((h₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh₁
  simp only [perronCompareKernel, Complex.ofReal_zero, zero_mul, add_zero, Complex.cpow_one,
    div_one]
  push_cast
  field_simp
  ring

theorem windowCompareKernel_zero {x h h₁ t₀ : ℝ} (hh : 0 ≤ h) (_hx : 0 < x) (ht₀ : 0 < t₀)
    (hxh₁ : 0 ≤ x + h₁) :
    windowCompareKernel x h h₁ t₀ 0 = 0 := by
  have hz : 2 * (0 : ℝ) * h * h₁ / x = 0 := by simp
  simp only [windowCompareKernel, abs_zero, max_eq_right ht₀.le, hz]
  rw [min_eq_right (by positivity : (0 : ℝ) ≤ 2 * h)]
  exact min_eq_left (by positivity)

/-- **The kernel domination, including the origin.** -/
theorem norm_perronCompareKernel_le_windowCompareKernel_all'
    {x h h₁ t₀ t : ℝ} (hx : 0 < x) (hh : 0 < h) (hle : h ≤ h₁) (ht₀ : 0 < t₀)
    (hlow : t₀ ≤ x / h₁) :
    ‖perronCompareKernel x h h₁ t‖ ≤ windowCompareKernel x h h₁ t₀ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · have hh₁ : 0 < h₁ := lt_of_lt_of_le hh hle
    rw [perronCompareKernel_zero (ne_of_gt hh₁), norm_zero,
      windowCompareKernel_zero hh.le hx ht₀ (by positivity)]
  · exact norm_perronCompareKernel_le_windowCompareKernel_all hx hh hle ht₀ hlow ht

/-- The comparison kernel is continuous in the ordinate. -/
theorem continuous_perronCompareKernel' {x h h₁ : ℝ} (hx : x ≠ 0) (hxh : x + h ≠ 0)
    (hxh₁ : x + h₁ ≠ 0) : Continuous (perronCompareKernel x h h₁) := by
  have hden : Continuous fun t : ℝ => ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I) := by fun_prop
  have hdenne : ∀ t : ℝ, ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro t h0
    have hre := congrArg Complex.re h0
    simp at hre
  have hpow : ∀ y : ℝ, y ≠ 0 →
      Continuous fun t : ℝ => ((y : ℝ) : ℂ) ^ ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I) := by
    intro y hy
    have hbase : Continuous fun z : ℂ => ((y : ℝ) : ℂ) ^ z :=
      continuous_iff_continuousAt.mpr fun _ =>
        continuousAt_const_cpow (by exact_mod_cast hy)
    exact hbase.comp hden
  have h1 : Continuous fun t : ℝ =>
      ((((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I))
      / ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I)) :=
    ((hpow _ hxh).sub (hpow _ hx)).div hden hdenne
  have h2 : Continuous fun t : ℝ =>
      ((((x + h₁ : ℝ) : ℂ) ^ ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I))
      / ((1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I)) :=
    ((hpow _ hxh₁).sub (hpow _ hx)).div hden hdenne
  exact h1.sub (continuous_const.mul h2)

/-- **The Perron comparison integral, bounded by the mixed-moment kernel.**  This is the step that
lets `integral_mixed_moment_windowCompare_le` consume the integral produced by
`norm_realWindowSum_compare_sub_integral_le`. -/
theorem norm_integral_perronPoly_compareKernel_le
    (c : ℕ → ℂ) (M : ℕ) {x h h₁ t₀ T : ℝ} (hx : 0 < x) (hh : 0 < h) (hle : h ≤ h₁)
    (ht₀ : 0 < t₀) (hlow : t₀ ≤ x / h₁) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, perronPoly c M 1 t * perronCompareKernel x h h₁ t‖
      ≤ ∫ t in (-T)..T, ‖perronPoly c M 1 t‖ * windowCompareKernel x h h₁ t₀ t := by
  have hab : (-T : ℝ) ≤ T := by linarith
  have hcP : Continuous fun t : ℝ => perronPoly c M 1 t := continuous_perronPoly c M 1
  have hh₁ : 0 < h₁ := lt_of_lt_of_le hh hle
  have hcK : Continuous fun t : ℝ => perronCompareKernel x h h₁ t :=
    continuous_perronCompareKernel' (ne_of_gt hx) (by positivity) (by positivity)
  have hcW : Continuous (windowCompareKernel x h h₁ t₀) := continuous_windowCompareKernel ht₀
  have hstep1 : ‖∫ t in (-T)..T, perronPoly c M 1 t * perronCompareKernel x h h₁ t‖
      ≤ ∫ t in (-T)..T, ‖perronPoly c M 1 t * perronCompareKernel x h h₁ t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  refine hstep1.trans ?_
  refine intervalIntegral.integral_mono_on hab
    ((hcP.mul hcK).norm.intervalIntegrable _ _)
    ((hcP.norm.mul hcW).intervalIntegrable _ _) ?_
  intro t _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_perronCompareKernel_le_windowCompareKernel_all' hx hh hle ht₀ hlow) (norm_nonneg _)

end

end RHTower.Sieve
