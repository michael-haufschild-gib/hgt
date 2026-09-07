import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomSourceTwelve
import GaloisForLFunctions.RHTower.ThetaCuspEvenCompensationCoefficient

/-! # Complete two-atom error for the source correction itself -/
namespace RHTower
noncomputable section

private theorem product_error {f g F G e h : ℝ}
    (hf : |f-F| ≤ e) (hg : |g-G| ≤ h) :
    |f*g-F*G| ≤ |F| *h+|G| *e+e*h := by
  have he : 0 ≤ e := (abs_nonneg _).trans hf
  have h1 := mul_le_mul_of_nonneg_left hg (abs_nonneg F)
  have h2 := mul_le_mul_of_nonneg_left hf (abs_nonneg G)
  have h3 := mul_le_mul hf hg (abs_nonneg _) he
  rw [show f*g-F*G = F*(g-G)+G*(f-F)+(f-F)*(g-G) by ring]
  have ht := abs_add_le (F*(g-G)+G*(f-F)) ((f-F)*(g-G))
  have ht' := abs_add_le (F*(g-G)) (G*(f-F))
  simp only [abs_mul] at ht ht'
  linarith only [h1, h2, h3, ht, ht']

/-- The same correction expression on the literal retained two-atom source. -/
def thetaCuspTwoAtomCompensationSource (x : ℝ) : ℝ :=
  3*thetaCuspTwoAtomSource x^2 + 2*x*thetaCuspTwoAtomSource x*deriv thetaCuspTwoAtomSource x

/-- Both linear source errors and both quadratic products remain in the correction bound. -/
def thetaCuspTwoAtomCompensationErrorBound (x : ℝ) : ℝ :=
  3*(2*|thetaCuspTwoAtomSource x| *thetaCuspTwoAtomSourceErrorBoundTwelve 0 x+
      thetaCuspTwoAtomSourceErrorBoundTwelve 0 x^2) +
    2*|x| *(|thetaCuspTwoAtomSource x| *thetaCuspTwoAtomSourceErrorBoundTwelve 1 x+
      |deriv thetaCuspTwoAtomSource x| *thetaCuspTwoAtomSourceErrorBoundTwelve 0 x+
      thetaCuspTwoAtomSourceErrorBoundTwelve 0 x*thetaCuspTwoAtomSourceErrorBoundTwelve 1 x)

/-- The literal correction has a complete finite two-atom error bound on the original middle ray. -/
theorem abs_thetaCuspCenterCompensationSource_sub_two_le {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspCenterCompensationSource x-thetaCuspTwoAtomCompensationSource x| ≤
      thetaCuspTwoAtomCompensationErrorBound x := by
  have h0 : |thetaCuspFullSource x-thetaCuspTwoAtomSource x| ≤
      thetaCuspTwoAtomSourceErrorBoundTwelve 0 x := by
    simpa only [iteratedDeriv_zero] using
      abs_thetaCuspFullSource_derivative_sub_two_le_twelve (n := 0) (by norm_num) hq
  have h1 : |deriv thetaCuspFullSource x-deriv thetaCuspTwoAtomSource x| ≤
      thetaCuspTwoAtomSourceErrorBoundTwelve 1 x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      abs_thetaCuspFullSource_derivative_sub_two_le_twelve (n := 1) (by norm_num) hq
  have hs := product_error h0 h0
  have hp := product_error h0 h1
  have he : thetaCuspCenterCompensationSource x-thetaCuspTwoAtomCompensationSource x =
      3*(thetaCuspFullSource x^2-thetaCuspTwoAtomSource x^2)+
        2*x*(thetaCuspFullSource x*deriv thetaCuspFullSource x-
          thetaCuspTwoAtomSource x*deriv thetaCuspTwoAtomSource x) := by
    unfold thetaCuspCenterCompensationSource thetaCuspTwoAtomCompensationSource
    ring
  rw [he]
  have ht := abs_add_le (3*(thetaCuspFullSource x^2-thetaCuspTwoAtomSource x^2))
    (2*x*(thetaCuspFullSource x*deriv thetaCuspFullSource x-
      thetaCuspTwoAtomSource x*deriv thetaCuspTwoAtomSource x))
  norm_num [abs_mul] at ht
  have hsm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3)
  have hpm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*|x| by positivity)
  simp only [← pow_two] at hsm
  unfold thetaCuspTwoAtomCompensationErrorBound
  nlinarith only [ht, hsm, hpm]

/-- One finite error bar controls every source coefficient in the proved rational band. -/
theorem abs_thetaCuspCenterCompensationSource_sub_two_mul_le {C x : ℝ}
    (hC : 1000000000000 ≤ C) (hCU : C ≤ 3000000000000)
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |C*thetaCuspCenterCompensationSource x-C*thetaCuspTwoAtomCompensationSource x| ≤
      3000000000000*thetaCuspTwoAtomCompensationErrorBound x := by
  have h := abs_thetaCuspCenterCompensationSource_sub_two_le hq
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ C by linarith)]
  exact mul_le_mul hCU h (abs_nonneg _) (by norm_num)

/-- The canonical coefficient has no remaining numerical or source-bound premise. -/
theorem abs_thetaCuspCanonicalEvenCompensationSource_sub_two_le {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeEvenCompensationCoefficient*thetaCuspCenterCompensationSource x-
      thetaCuspNativeEvenCompensationCoefficient*thetaCuspTwoAtomCompensationSource x| ≤
      3000000000000*thetaCuspTwoAtomCompensationErrorBound x :=
  abs_thetaCuspCenterCompensationSource_sub_two_mul_le
    thetaCuspNativeEvenCompensationCoefficient_bounds.1.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le hq

end
end RHTower
