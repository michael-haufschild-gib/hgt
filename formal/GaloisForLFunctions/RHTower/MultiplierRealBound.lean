import GaloisForLFunctions.HTGeometry.ExpMultiplierRapidDecay

/-!
# The smoothing multiplier on the real axis

`logSmoothMultiplier k w = ∫ k(x)e^{wx}dx` with `k` supported in `|x| ≤ R` and `∫|k| = 1` satisfies

`‖logSmoothMultiplier k w‖ ≤ e^{R·|Re w|}`.

On the real axis this is the only thing needed to see that smoothing does not destroy the aperture
decay of the Mellin transform: it multiplies `b^{-σ}` by at most `e^{Rσ}`, and `e^R/b < 1` as soon
as `R < log b`.

## Main results

* `norm_logSmoothMultiplier_le_exp`
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_logSmoothMultiplier_le_exp {k : ℝ → ℝ} (hk : Continuous k) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) (hint : (∫ x : ℝ, |k x|) = 1) (w : ℂ) :
    ‖logSmoothMultiplier k w‖ ≤ Real.exp (R * |w.re|) := by
  have hks : HasCompactSupport k := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) ?_
    intro x hx
    refine hsupp x ?_
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rcases le_or_gt x 0 with hx0 | hx0
      · rw [abs_of_nonpos hx0]; linarith
      · linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x)]; linarith
  have hcont : Continuous fun x : ℝ => ((k x : ℝ) : ℂ) * Complex.exp (w * x) :=
    continuous_expWeight hk w
  have hintegrable : Integrable (fun x : ℝ => ((k x : ℝ) : ℂ) * Complex.exp (w * x)) volume := by
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_right ?_
    exact (hks.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp))
  have hbound : ∀ x : ℝ, ‖((k x : ℝ) : ℂ) * Complex.exp (w * x)‖
      ≤ |k x| * Real.exp (R * |w.re|) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases eq_or_ne (k x) 0 with h0 | h0
    · rw [h0]
      simp
    · have hxR : |x| < R := by
        by_contra hcon
        exact h0 (hsupp x (not_lt.1 hcon))
      have hexp : ‖Complex.exp (w * (x : ℂ))‖ = Real.exp (w.re * x) := by
        rw [Complex.norm_exp]
        congr 1
        simp
      rw [hexp]
      have hle : w.re * x ≤ R * |w.re| := by
        have h1 : w.re * x ≤ |w.re * x| := le_abs_self _
        have h2 : |w.re * x| = |w.re| * |x| := abs_mul _ _
        have h3 : |w.re| * |x| ≤ |w.re| * R := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hxR) (abs_nonneg _)
        calc w.re * x ≤ |w.re * x| := h1
          _ = |w.re| * |x| := h2
          _ ≤ |w.re| * R := h3
          _ = R * |w.re| := by ring
      have hmono : Real.exp (w.re * x) ≤ Real.exp (R * |w.re|) := Real.exp_le_exp.2 hle
      have habs : (0:ℝ) ≤ |k x| := abs_nonneg _
      nlinarith [Real.exp_pos (w.re * x)]
  calc ‖logSmoothMultiplier k w‖
      ≤ ∫ x : ℝ, ‖((k x : ℝ) : ℂ) * Complex.exp (w * x)‖ := by
        rw [logSmoothMultiplier]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, |k x| * Real.exp (R * |w.re|) := by
        refine integral_mono hintegrable.norm ?_ hbound
        have habs : Integrable (fun x : ℝ => |k x|) volume := by
          have : Integrable k volume := hk.integrable_of_hasCompactSupport hks
          exact this.abs
        exact habs.mul_const _
    _ = Real.exp (R * |w.re|) := by
        rw [integral_mul_const, hint, one_mul]

end

end GaloisForLFunctions.HTGeometry
