import GaloisForLFunctions.RHTower.LevinsonDetectorLine

/-!
# Positivity of Levinson's archimedean weight at the classical positive parameter

The detector coefficients for `ζ + λζ'` carry `1 - λ log n`, hence the classical choice is
`λ = 1 / log T`, not a negative parameter.  On the full counting window `20 ≤ τ ≤ T`, the
digamma term is at most `log T + 1`; therefore the critical-line weight

`Y = 2 - (Re ψ(1/4+iτ/2) - log π) / log T`

is strictly positive.  This supplies the sign condition needed by the polar/counting consumer
without reversing the arithmetic detector.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- The real digamma displacement on the critical line is bounded by `log T + 1` throughout
`[20,T]`. -/
theorem re_digamma_quarter_sub_log_pi_lt_log_add_one
    {T τ : ℝ} (hT : 20 ≤ T) (hτ : τ ∈ Set.Icc (20 : ℝ) T) :
    (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re -
        Real.log Real.pi < Real.log T + 1 := by
  have hτ0 : (0 : ℝ) < τ := by linarith [hτ.1]
  have hT0 : (0 : ℝ) < T := by linarith
  have hb := re_digamma_vertical_bound_uncond (σ := 1 / 4) (t := τ / 2)
    (by norm_num) (by linarith)
  have hupper :
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re ≤
        (1 / 2 : ℝ) * Real.log ((1 / 4 : ℝ) ^ 2 + (τ / 2) ^ 2) +
          (1 / (τ / 2) ^ 2 + Real.pi / (2 * (τ / 2))) := by
    linarith [(abs_le.mp hb).2]
  have harg : (0 : ℝ) < (1 / 4 : ℝ) ^ 2 + (τ / 2) ^ 2 := by positivity
  have hargT : (1 / 4 : ℝ) ^ 2 + (τ / 2) ^ 2 ≤ T ^ 2 := by
    nlinarith [hτ.2, hτ0, hT0]
  have hlogarg : Real.log ((1 / 4 : ℝ) ^ 2 + (τ / 2) ^ 2) ≤ Real.log (T ^ 2) :=
    Real.log_le_log harg hargT
  have hlogTsq : Real.log (T ^ 2) = 2 * Real.log T := by
    rw [Real.log_pow]
    norm_num
  have herr1 : 1 / (τ / 2) ^ 2 ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hτ.1]
  have herr2 : Real.pi / (2 * (τ / 2)) < 1 / 5 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d2, hτ.1]
  have hlogpi : (0 : ℝ) < Real.log Real.pi :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  rw [hlogTsq] at hlogarg
  nlinarith

/-- At `λ = 1/log T`, Levinson's critical-line weight has positive real part on the whole
counting window. -/
theorem levinsonY_line_re_pos_reciprocal_log
    {T τ : ℝ} (hT : 20 ≤ T) (hτ : τ ∈ Set.Icc (20 : ℝ) T) :
    0 < (levinsonY (((1 : ℝ) / Real.log T : ℝ) : ℂ) (linePt τ)).re := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (1 : ℝ) < Real.log T := by
    rw [Real.lt_log_iff_exp_lt hT0]
    linarith [Real.exp_one_lt_d9]
  have hd := re_digamma_quarter_sub_log_pi_lt_log_add_one hT hτ
  rw [levinsonY_line_eq, Complex.ofReal_re]
  have hlogT0 : (0 : ℝ) < Real.log T := by linarith
  rw [one_div]
  have hmul : (Real.log T)⁻¹ *
      ((Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re -
        Real.log Real.pi) < 2 := by
    rw [inv_mul_lt_iff₀ hlogT0]
    nlinarith
  linarith

/-- In particular, the classical positive detector weight never vanishes on `[20,T]`. -/
theorem levinsonY_line_ne_zero_reciprocal_log
    {T τ : ℝ} (hT : 20 ≤ T) (hτ : τ ∈ Set.Icc (20 : ℝ) T) :
    levinsonY (((1 : ℝ) / Real.log T : ℝ) : ℂ) (linePt τ) ≠ 0 := by
  intro hzero
  have := levinsonY_line_re_pos_reciprocal_log hT hτ
  rw [hzero, Complex.zero_re] at this
  linarith

end RHTower

end
