import GaloisForLFunctions.RHTower.XiMarkedIslandSeparation

/-!
# Simple marked Xi values arbitrarily far right

Uniform positivity of the real logarithmic derivative makes every sufficiently
far-right nonzero value regular. The established value-occurrence theorem
therefore supplies simple minus-one points for every real exponential tilt.
-/

open Complex Metric Set

namespace RHTower

/-- Every real mark has simple minus-one points arbitrarily far right, isolated from all other marks. -/
theorem exists_xi_tilt_simple_minus_one (a R : ℝ) :
    ∃ s : ℂ, R < s.re ∧
      xi s * Complex.exp (-(a : ℂ) * s) = -1 ∧
      analyticOrderAt (fun z => 1 + xi z * Complex.exp (-(a : ℂ) * z)) s = 1 ∧
      ∀ b : ℝ, b ≠ a → xi s * Complex.exp (-(b : ℂ) * s) ≠ -1 := by
  obtain ⟨B, hB2, hB⟩ := exists_re_logDeriv_xi_ge_halfPlane (a + 1)
  obtain ⟨s, hs, hvalue⟩ := exists_xi_tilt_eq_of_nonzero a (max B R)
    (by have := le_max_left B R; linarith)
    (w := -1) (by norm_num)
  have hsB : B < s.re := (le_max_left _ _).trans_lt hs
  have hspos : 0 < s.re := by linarith
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_lt_re (by linarith)
  let f : ℂ → ℂ := fun z => 1 + xi z * Complex.exp (-(a : ℂ) * z)
  have hd : HasDerivAt f
      ((logDeriv xi s - (a : ℂ)) * (xi s * Complex.exp (-(a : ℂ) * s))) s := by
    have hd0 := ((xi_differentiable s).hasDerivAt.mul
      (((hasDerivAt_id s).const_mul (-(a : ℂ))).cexp)).const_add 1
    refine hd0.congr_deriv ?_
    simp only [id_eq]
    rw [logDeriv_apply]
    field_simp [hxi]
    ring
  have hlogne : logDeriv xi s - (a : ℂ) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    have := hB s hsB.le
    linarith
  have hdne : deriv f s ≠ 0 := by
    rw [hd.deriv]
    exact mul_ne_zero hlogne (by rw [hvalue]; norm_num)
  have hfzero : f s = 0 := by
    change 1 + xi s * Complex.exp (-(a : ℂ) * s) = 0
    rw [hvalue]
    ring
  have hfa : AnalyticAt ℂ f s := by
    have hf : Differentiable ℂ f := (xi_differentiable.mul (by fun_prop)).const_add 1
    exact hf.analyticAt s
  refine ⟨s, (le_max_right _ _).trans_lt hs, hvalue,
    hfa.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfzero hdne, fun b hba hb => ?_⟩
  have hw : xi s * Complex.exp (-(a : ℂ) * s) =
      Complex.exp ((Real.pi : ℂ) * I) := by rw [Complex.exp_pi_mul_I, hvalue]
  have hnorm := norm_xi_tilt_of_log_value (b := b) hw
  rw [hb] at hnorm
  norm_num only [norm_neg, norm_one, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    zero_add] at hnorm
  have hh : (a - b) * s.re = 0 := by
    simpa only [Real.exp_eq_one_iff] using hnorm.symm
  exact (mul_ne_zero (sub_ne_zero.mpr hba.symm) hspos.ne') hh

end RHTower
