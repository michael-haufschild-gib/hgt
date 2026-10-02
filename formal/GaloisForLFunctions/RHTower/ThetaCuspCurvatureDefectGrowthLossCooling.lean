import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthStableComponents

/-!
# Support-gap cooling of actual growth-transfer losses

The stable deep moments satisfy the rate-eight comparison. Every product
M0^(k+1)*Mj has its exact source derivative and cools at least at rate
3(k+2). These are literal source inequalities. The dominant pair's relative
cooling comparison and the absorption residual's center sign remain open.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory
noncomputable section

theorem deepMoment_gap {q : ℝ} (hq : 0 < q) (j : ℕ) :
    8*thetaCuspDeepTailMoment q j ≤ thetaCuspDeepTailMoment q (j+1) := by
  unfold thetaCuspDeepTailMoment
  rw [←integral_const_mul]
  apply integral_mono_ae
    ((integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq).const_mul 8)
    (integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure (j+1) hq)
  filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
  rw [pow_succ]
  have h := mul_le_mul_of_nonneg_right ht
    (mul_nonneg (pow_nonneg (by linarith : 0 ≤ t) j) (Real.exp_pos (-q*t)).le)
  nlinarith

theorem sourceMomentProduct_hasDerivAt {q : ℝ} (hq : 0 < q) (k j : ℕ) :
    HasDerivAt (fun t => thetaCuspHigherLikelihoodSpectralMoment t 0^(k+1)*
      thetaCuspHigherLikelihoodSpectralMoment t j)
      (-((k+1:ℕ):ℝ)*thetaCuspHigherLikelihoodSpectralMoment q 0^k*
        thetaCuspHigherLikelihoodSpectralMoment q 1*thetaCuspHigherLikelihoodSpectralMoment q j-
        thetaCuspHigherLikelihoodSpectralMoment q 0^(k+1)*thetaCuspHigherLikelihoodSpectralMoment q (j+1)) q := by
  have h := ((hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment 0 hq).pow (k+1)).mul
    (hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment j hq)
  exact h.congr_deriv (by simp only [Pi.pow_apply,Nat.add_sub_cancel,Nat.zero_add]; ring)

theorem sourceMomentProduct_cooling {q : ℝ} (hq : 0 < q) (k j : ℕ) :
    -((k+1:ℕ):ℝ)*thetaCuspHigherLikelihoodSpectralMoment q 0^k*
        thetaCuspHigherLikelihoodSpectralMoment q 1*thetaCuspHigherLikelihoodSpectralMoment q j-
        thetaCuspHigherLikelihoodSpectralMoment q 0^(k+1)*thetaCuspHigherLikelihoodSpectralMoment q (j+1) ≤
      -3*((k+2:ℕ):ℝ)*thetaCuspHigherLikelihoodSpectralMoment q 0^(k+1)*
        thetaCuspHigherLikelihoodSpectralMoment q j := by
  have h0 := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := q) 0
  have hj := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := q) j
  have h1 := mul_le_mul_of_nonneg_left
    (three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hq 0)
    (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ ((k+1:ℕ):ℝ)) (pow_nonneg h0 k)) hj)
  have h2 := mul_le_mul_of_nonneg_left
    (three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hq j) (pow_nonneg h0 (k+1))
  simp only [pow_succ,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h1 h2 ⊢
  nlinarith

end
end RHTower.ThetaCuspDefect
