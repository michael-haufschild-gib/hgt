import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralTwoHeadTruncation

/-!
# Finite smooth AFE at Levinson's displaced abscissa

The standard shift `σ₀ = 1/2 - R/log T` lies in the open critical strip as
soon as `R > 0` and `exp(2R) < T`.  The general two-head truncation therefore
specializes without any analytic hypothesis.
-/

noncomputable section

namespace RHTower

open Complex

/-- Levinson's displaced real abscissa. -/
def levinsonAbscissa (R T : ℝ) : ℝ := 1 / 2 - R / Real.log T

/-- Complex point on Levinson's displaced vertical line. -/
def levinsonPoint (R T t : ℝ) : ℂ :=
  (levinsonAbscissa R T : ℂ) + (t : ℂ) * I

theorem two_mul_lt_log_of_exp_two_mul_lt
    {R T : ℝ} (hT : Real.exp (2 * R) < T) :
    2 * R < Real.log T := by
  have hT0 : 0 < T := lt_trans (Real.exp_pos _) hT
  exact (Real.lt_log_iff_exp_lt hT0).2 hT

theorem levinsonAbscissa_pos
    {R T : ℝ} (hR : 0 < R) (hT : Real.exp (2 * R) < T) :
    0 < levinsonAbscissa R T := by
  have hlog : 2 * R < Real.log T := two_mul_lt_log_of_exp_two_mul_lt hT
  have hlog0 : 0 < Real.log T := by linarith
  unfold levinsonAbscissa
  have hdiv : R / Real.log T < 1 / 2 := by
    rw [div_lt_iff₀ hlog0]
    nlinarith
  linarith

theorem levinsonAbscissa_lt_half
    {R T : ℝ} (hR : 0 < R) (hT : Real.exp (2 * R) < T) :
    levinsonAbscissa R T < 1 / 2 := by
  have hlog : 2 * R < Real.log T := two_mul_lt_log_of_exp_two_mul_lt hT
  have hlog0 : 0 < Real.log T := by linarith
  unfold levinsonAbscissa
  have : 0 < R / Real.log T := div_pos hR hlog0
  linarith

theorem levinsonPoint_re (R T t : ℝ) :
    (levinsonPoint R T t).re = levinsonAbscissa R T := by
  simp [levinsonPoint]

theorem levinsonPoint_im (R T t : ℝ) :
    (levinsonPoint R T t).im = t := by
  simp [levinsonPoint]

theorem levinsonPoint_ne_one
    {R T t : ℝ} (hR : 0 < R) (hT : Real.exp (2 * R) < T) :
    levinsonPoint R T t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [levinsonPoint_re] at hre
  simp only [Complex.one_re] at hre
  have hhalf := levinsonAbscissa_lt_half hR hT
  linarith

/-- Both Gaussian AFE heads truncate with explicit errors on Levinson's
displaced line.  The direct decay exponent is specialized to `A = 1`. -/
theorem exists_riemannZeta_levinsonPoint_sub_two_smoothAFE_heads_le
    {R T : ℝ} (hR : 0 < R) (hT : Real.exp (2 * R) < T)
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ Ld Lu : ℕ, 1 ≤ Ld → 1 ≤ Lu →
      ‖riemannZeta (levinsonPoint R T t) -
          ((∑ n ∈ Finset.range Ld,
              (((n + 1 : ℕ) : ℂ)) ^ (-levinsonPoint R T t) *
                smoothAFECutoff (((n + 1 : ℕ) : ℝ) / x)) -
            (∑ n ∈ Finset.range Lu,
              smoothAFEZetaDualCoefficientGeneral
                (levinsonPoint R T t) x n) -
            smoothAFEZetaShiftedPoleResidue (levinsonPoint R T t) x)‖ ≤
        C * x *
            (((Ld : ℝ)) ^ (-levinsonAbscissa R T) /
              levinsonAbscissa R T) +
          K * (((Lu : ℝ)) ^ (levinsonAbscissa R T - 1) /
            (1 - levinsonAbscissa R T)) := by
  have h0 : 0 < (levinsonPoint R T t).re := by
    rw [levinsonPoint_re]
    exact levinsonAbscissa_pos hR hT
  have h1 : (levinsonPoint R T t).re < 1 := by
    rw [levinsonPoint_re]
    linarith [levinsonAbscissa_lt_half hR hT]
  obtain ⟨C, K, hC0, hK0, hbound⟩ :=
    exists_riemannZeta_sub_two_smoothAFE_heads_le
      (A := (1 : ℝ)) (by norm_num) hx (levinsonPoint_ne_one hR hT)
      h0 h1 (by linarith)
  refine ⟨C, K, hC0, hK0, fun Ld Lu hLd hLu => ?_⟩
  simpa only [Real.rpow_one, levinsonPoint_re,
    show 1 - (levinsonAbscissa R T + 1) = -levinsonAbscissa R T by ring,
    show levinsonAbscissa R T + 1 - 1 = levinsonAbscissa R T by ring]
    using hbound Ld Lu hLd hLu

end RHTower
