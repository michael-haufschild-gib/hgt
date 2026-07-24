import GaloisForLFunctions.RHTower.EvenIndexHermitianAbelBound
import GaloisForLFunctions.HTGeometry.PowerSeriesEventualSignRecurrence

/-!
# Radial blow-up forces even-index sign recurrence

If the Hermitian radial profile `‖∑' a_N r^N‖` is unbounded as the radius approaches `1`, then the
real parts of the even-index mixed additive convolution powers are positive at cofinally many indices
(`frequently_re_pos_of_norm_unbounded`).

This couples two facts.  The radial upper bound `norm_pow_sq_le_two_mul_tsum_evenIndex_re` shows the
even-index Abel series of the real parts dominates half the squared radial profile, so a radially
unbounded profile makes that Abel series exceed any finite prefix bound; the coefficient-recurrence
engine `frequently_pos_of_forall_exists_tsum_gt` then converts unbounded Abel growth into cofinally
many positive coefficients.  The remaining analytic input for the pole-frontier statement is that a
right half-plane Dirichlet pole produces exactly such radial blow-up, supplied by
`HTGeometry.not_isBigO_zero_of_mellin_eq_Gamma_mul`.
-/

open Complex Filter
open scoped BigOperators Topology

namespace RHTower

/-- **Even-index sign recurrence from radial blow-up.**  For an absolutely convergent coefficient
profile whose Hermitian radial modulus is unbounded as the radius tends to `1`, the real parts of the
`2k`-fold even-index mixed additive convolution powers are positive at infinitely many indices. -/
theorem frequently_re_pos_of_norm_unbounded (a : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k)
    (habs : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun N => ‖a N * (r : ℂ) ^ N‖))
    (hunb : ∀ B : ℝ, ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ B < ‖∑' N : ℕ, a N * (r : ℂ) ^ N‖) :
    ∃ᶠ q in Filter.atTop, 0 < (mixedAdditiveConvolutionPower a k (2 * q)).re := by
  apply GaloisForLFunctions.HTGeometry.frequently_pos_of_forall_exists_tsum_gt
  · intro u hu0 hu1
    have hr0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
    have hr1 : Real.sqrt u < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt hu0 hu1
    have hru : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0
    have hcomplex := summable_evenIndex_mixedAdditive a (habs (Real.sqrt u) hr0 hr1) k
    refine (hcomplex.map Complex.reCLM.toLinearMap.toAddMonoidHom Complex.reCLM.continuous).congr
      (fun q => ?_)
    show (mixedAdditiveConvolutionPower a k (2 * q) * (Real.sqrt u : ℂ) ^ (2 * q)).re
      = (mixedAdditiveConvolutionPower a k (2 * q)).re * u ^ q
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, pow_mul, hru]
  · intro Q
    set P := ∑ q ∈ Finset.range Q, |(mixedAdditiveConvolutionPower a k (2 * q)).re| with hP
    have hP0 : 0 ≤ P := Finset.sum_nonneg (fun q _ => abs_nonneg _)
    obtain ⟨r, hr0, hr1, hrB⟩ := hunb (2 * P + 1)
    refine ⟨r ^ 2, by positivity, pow_lt_one₀ hr0 hr1 two_ne_zero, ?_⟩
    have hbound := norm_pow_sq_le_two_mul_tsum_evenIndex_re a (habs r hr0 hr1) k
    have hnorm : ‖(∑' N : ℕ, a N * (r : ℂ) ^ N) ^ k‖ ^ 2
        = ‖∑' N : ℕ, a N * (r : ℂ) ^ N‖ ^ (2 * k) := by
      rw [norm_pow, ← pow_mul, mul_comm]
    have hge1 : (1 : ℝ) ≤ ‖∑' N : ℕ, a N * (r : ℂ) ^ N‖ := by linarith [hrB, hP0]
    have hself : ‖∑' N : ℕ, a N * (r : ℂ) ^ N‖ ≤ ‖∑' N : ℕ, a N * (r : ℂ) ^ N‖ ^ (2 * k) :=
      le_self_pow₀ hge1 (by omega)
    have hsumeq : (∑' q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re * (r ^ 2) ^ q)
        = ∑' q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re * r ^ (2 * q) := by
      refine tsum_congr (fun q => ?_)
      rw [pow_mul]
    rw [hsumeq]
    nlinarith [hbound, hnorm, hself, hrB, hP0]

end RHTower
