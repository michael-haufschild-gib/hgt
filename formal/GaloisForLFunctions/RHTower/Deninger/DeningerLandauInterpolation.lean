import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A Landau interpolation inequality

Writing the increment of a smooth function as the integral of its derivative and comparing that
derivative with its value at the left endpoint gives

`‖u'(x)‖ ≤ 2 sup_{[x, x+δ]} ‖u‖ / δ + M δ`,

where `M` bounds the second derivative.  Letting the window `δ` shrink with the size of `u`
converts *decay of `u` together with boundedness of `u''`* into decay of `u'`.

This is the mechanism that upgrades a rapidly decreasing function with bounded derivatives of every
order to a Schwartz function, with no differentiation of the defining series.

* `deningerLandau_deriv_le` : **`‖u'(x)‖ ≤ 2ε/δ + Mδ`.**
-/

namespace RHTower

open MeasureTheory

open scoped ContDiff

noncomputable section

/-- **The Landau interpolation inequality.**  A smooth function which is small on a window has
small derivative at the left endpoint, up to the second-derivative bound times the window
length. -/
theorem deningerLandau_deriv_le {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) {M : ℝ}
    (hM : ∀ y : ℝ, ‖deriv (deriv u) y‖ ≤ M) {x δ ε : ℝ} (hδ : 0 < δ)
    (hε : ∀ y ∈ Set.Icc x (x + δ), ‖u y‖ ≤ ε) :
    ‖deriv u x‖ ≤ 2 * ε / δ + M * δ := by
  have hd1 : Differentiable ℝ u := hu.differentiable (by simp)
  have hu' : ContDiff ℝ ∞ (deriv u) := by
    have h := hu.iterate_deriv 1
    simpa using h
  have hd2 : Differentiable ℝ (deriv u) := hu'.differentiable (by simp)
  have hcont : Continuous (deriv u) := hd2.continuous
  have hxle : x ≤ x + δ := by linarith
  have hftc : (∫ s in x..(x + δ), deriv u s) = u (x + δ) - u x :=
    intervalIntegral.integral_deriv_eq_sub (fun y _ => hd1.differentiableAt)
      (hcont.intervalIntegrable _ _)
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM x)
  have hlip : ∀ s ∈ Set.uIoc x (x + δ), ‖deriv u s - deriv u x‖ ≤ M * δ := by
    intro s hs
    have hsmem : s ∈ Set.Icc x (x + δ) := by
      rw [Set.uIoc_of_le hxle] at hs
      exact ⟨le_of_lt hs.1, hs.2⟩
    have hconv : Convex ℝ (Set.Icc x (x + δ)) := convex_Icc _ _
    have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le
      (fun y _ => hd2.differentiableAt) (fun y _ => hM y)
      (Set.left_mem_Icc.mpr hxle) hsmem
    refine le_trans hmvt ?_
    have hsx : ‖s - x‖ ≤ δ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hsmem.1])]
      linarith [hsmem.2]
    exact mul_le_mul_of_nonneg_left hsx hMnn
  have hsplit : (∫ s in x..(x + δ), (deriv u s - deriv u x))
      = (u (x + δ) - u x) - δ • deriv u x := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      intervalIntegrable_const, hftc, intervalIntegral.integral_const]
    congr 2
    ring
  have hnormint : ‖∫ s in x..(x + δ), (deriv u s - deriv u x)‖ ≤ M * δ * |x + δ - x| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hlip
  rw [hsplit, show x + δ - x = δ by ring, abs_of_pos hδ] at hnormint
  have hu1 : ‖u (x + δ)‖ ≤ ε := hε _ (Set.right_mem_Icc.mpr hxle)
  have hu0 : ‖u x‖ ≤ ε := hε _ (Set.left_mem_Icc.mpr hxle)
  have hsmul : ‖δ • deriv u x‖ = δ * ‖deriv u x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  have hstep : δ * ‖deriv u x‖ ≤ 2 * ε + M * δ * δ := by
    have htri : ‖δ • deriv u x‖
        ≤ ‖u (x + δ) - u x‖ + ‖(u (x + δ) - u x) - δ • deriv u x‖ := by
      have hnorm := norm_sub_le (u (x + δ) - u x)
        ((u (x + δ) - u x) - δ • deriv u x)
      have hrw : (u (x + δ) - u x) - ((u (x + δ) - u x) - δ • deriv u x)
          = δ • deriv u x := by
        abel
      rwa [hrw] at hnorm
    have hdiff : ‖u (x + δ) - u x‖ ≤ 2 * ε :=
      le_trans (norm_sub_le _ _) (by linarith)
    rw [hsmul] at htri
    linarith
  have hfinal : ‖deriv u x‖ ≤ (2 * ε + M * δ * δ) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  refine le_trans hfinal (le_of_eq ?_)
  field_simp

end

end RHTower
