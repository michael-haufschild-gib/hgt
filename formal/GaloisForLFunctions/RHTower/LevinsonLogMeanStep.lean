import Mathlib

/-!
# The logarithmic mean-value step of Levinson's method

Littlewood's lemma converts a zero count in a half-strip into `\int \log\|f\|` along the left
edge.  Levinson's method then replaces that logarithmic integral by the *second* moment of `f`,
which is what a mollified mean-value theorem computes.  The passage is Jensen's inequality for the
concave logarithm; the proof here is the elementary tangent-line bound `\log u \le u/c + \log c - 1`
at the optimal `c`, which is the mean square itself.
-/

open MeasureTheory intervalIntegral Set


namespace RHTower

/-- **The logarithmic mean-value step.**  On an interval where a continuous function has no zero,
the mean of `log ‖f‖` is at most half the logarithm of the mean of `‖f‖²`.  This is Jensen's
inequality for the concave logarithm, obtained here from the elementary tangent-line bound
`log u ≤ u/c + log c − 1`. -/
private theorem two_mul_integral_log_norm_le {f : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) (hf : ∀ t ∈ Icc a b, f t ≠ 0) :
    2 * (∫ t in a..b, Real.log ‖f t‖)
      ≤ (b - a) * Real.log ((b - a)⁻¹ * ∫ t in a..b, ‖f t‖ ^ (2 : ℕ)) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hnorm : ContinuousOn (fun t => ‖f t‖ ^ (2 : ℕ)) (Icc a b) := (hcont.norm).pow 2
  have hnormInt : IntervalIntegrable (fun t => ‖f t‖ ^ (2 : ℕ)) volume a b :=
    (hnorm.mono (by rw [uIcc_of_le hab.le])).intervalIntegrable
  have hlogInt : IntervalIntegrable (fun t => Real.log ‖f t‖) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab.le]
    exact ContinuousOn.log hcont.norm (fun t ht => norm_ne_zero_iff.mpr (hf t ht))
  -- the mean square is positive
  have hpos : 0 < ∫ t in a..b, ‖f t‖ ^ (2 : ℕ) := by
    have hcontOn : ContinuousOn (fun t => ‖f t‖ ^ (2 : ℕ)) (uIcc a b) := by
      rw [uIcc_of_le hab.le]; exact hnorm
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hnormInt (fun t ht => ?_) hab
    have htI : t ∈ Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have := hf t htI
    positivity
  set c : ℝ := (b - a)⁻¹ * ∫ t in a..b, ‖f t‖ ^ (2 : ℕ) with hc
  have hc0 : 0 < c := by positivity
  -- the pointwise tangent-line bound
  have hpoint : ∀ t ∈ Icc a b,
      2 * Real.log ‖f t‖ ≤ ‖f t‖ ^ (2 : ℕ) / c + Real.log c - 1 := by
    intro t ht
    have hne : ‖f t‖ ≠ 0 := norm_ne_zero_iff.mpr (hf t ht)
    have hu : 0 < ‖f t‖ ^ (2 : ℕ) := by positivity
    have hquot : 0 < ‖f t‖ ^ (2 : ℕ) / c := by positivity
    have hlog := Real.log_le_sub_one_of_pos hquot
    rw [Real.log_div (ne_of_gt hu) (ne_of_gt hc0)] at hlog
    have hsq : Real.log (‖f t‖ ^ (2 : ℕ)) = 2 * Real.log ‖f t‖ := by
      rw [Real.log_pow]; push_cast; ring
    rw [hsq] at hlog
    linarith
  have hmono : (∫ t in a..b, 2 * Real.log ‖f t‖)
      ≤ ∫ t in a..b, (‖f t‖ ^ (2 : ℕ) / c + Real.log c - 1) := by
    refine intervalIntegral.integral_mono_on hab.le (hlogInt.const_mul 2) ?_ hpoint
    exact ((hnormInt.div_const c).add intervalIntegrable_const).sub intervalIntegrable_const
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [intervalIntegral.integral_sub ((hnormInt.div_const c).add intervalIntegrable_const)
    intervalIntegrable_const, intervalIntegral.integral_add (hnormInt.div_const c)
    intervalIntegrable_const, intervalIntegral.integral_div] at hmono
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hcancel : (∫ t in a..b, ‖f t‖ ^ (2 : ℕ)) / c = b - a := by
    rw [hc]
    field_simp
  rw [hcancel] at hmono
  linarith

end RHTower
