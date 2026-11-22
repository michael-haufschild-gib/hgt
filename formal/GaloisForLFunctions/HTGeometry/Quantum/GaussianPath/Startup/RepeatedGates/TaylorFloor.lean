import Mathlib.Analysis.Calculus.Taylor

/-! # A nonzero second derivative forces a quadratic norm floor -/
open Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem leading_floor {f : ℝ→E} {k : ℕ} (hf : ContDiff ℝ k f) {v : E} (hv : v ≠ 0)
    (he : ∀ t, taylorWithinEval f k univ 0 t=t^k • v) :
    ∀ᶠ t : ℝ in 𝓝 0, (‖v‖/2)*‖t^k‖ ≤ ‖f t‖ := by
  have h := (taylor_isLittleO_univ (x₀:=0) hf).bound (half_pos (norm_pos_iff.mpr hv))
  filter_upwards [h] with t ht
  rw [he,sub_zero] at ht
  have h' : ‖t^k‖*‖v‖ ≤ ‖f t‖+‖f t-t^k • v‖ := by
    rw [←norm_smul]
    calc _ = ‖f t-(f t-t^k • v)‖ := by congr 1; abel
         _ ≤ _ := norm_sub_le _ _
  linarith only [ht,h']

/-- When the first derivative survives, its linear bound already
dominates the quadratic scale. Otherwise the second derivative leads. -/
theorem second_deriv_floor {f : ℝ→E} (hf : ContDiff ℝ 2 f) (h₀ : f 0=0)
    (h₂ : iteratedDeriv 2 f 0 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in 𝓝 0, c*t^2 ≤ ‖f t‖ := by
  have h₁ (t : ℝ) : taylorWithinEval f 1 univ 0 t=t • deriv f 0 := by
    rw [taylorWithinEval_succ f 0]
    simp [h₀,iteratedDerivWithin_univ,iteratedDeriv_one]
  by_cases h : deriv f 0=0
  · let v := (1/2 : ℝ) • iteratedDeriv 2 f 0
    have hv : v ≠ 0 := smul_ne_zero (by norm_num) h₂
    have he (t : ℝ) : taylorWithinEval f 2 univ 0 t=t^2 • v := by
      rw [taylorWithinEval_succ f 1,h₁,h,smul_zero,zero_add,iteratedDerivWithin_univ]
      simp only [v,smul_smul,sub_zero]
      congr 1
      norm_num
      ring
    refine ⟨‖v‖/2,half_pos (norm_pos_iff.mpr hv),?_⟩
    filter_upwards [leading_floor hf hv he] with t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t)] using ht
  · have he (t : ℝ) : taylorWithinEval f 1 univ 0 t=t^1 • deriv f 0 := by rw [h₁,pow_one]
    have hd := leading_floor (hf.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)) h he
    have hpos := half_pos (norm_pos_iff.mpr h)
    refine ⟨_,hpos,?_⟩
    have hwin : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) zero_lt_one] with t ht
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
    filter_upwards [hd,hwin] with t ht hwin
    rw [pow_one,Real.norm_eq_abs] at ht
    have hs : t^2 ≤ |t| := by
      rw [←sq_abs,pow_two]; exact mul_le_of_le_one_right (abs_nonneg _) hwin.le
    exact (mul_le_mul_of_nonneg_left hs hpos.le).trans ht

end GaloisForLFunctions.HTGeometry.RepeatedGates
