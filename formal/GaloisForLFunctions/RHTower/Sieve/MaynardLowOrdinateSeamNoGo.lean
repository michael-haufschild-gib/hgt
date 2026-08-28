import GaloisForLFunctions.RHTower.Sieve.MaynardDerivativeCountDuality
import GaloisForLFunctions.RHTower.Sieve.MaynardTwoAlternativeGapReceiver
import GaloisForLFunctions.RHTower.Sieve.MaynardRouteTGlobalRStarCoverage

namespace RHTower.Sieve

noncomputable section

/-- At the bottom common-mode shell, the exact trivial/derivative seam is `alpha = 7/8`. -/
theorem routeT_muEight_derivativeSeam_classification :
    (8 : ℝ) * (1 - 7 / 8) = 1 ∧
      maynardDerivativeComplementHeightExponent 8 (7 / 8) 0 = 1 ∧
      maynardDerivativeComplementLengthExponent 8 (7 / 8) = 0 ∧
      1 + 8 * (1 + routeTGapMomentNu - 2 * (7 / 8)) < 0 := by
  constructor
  · norm_num
  constructor
  · norm_num [maynardDerivativeComplementHeightExponent]
  constructor
  · norm_num [maynardDerivativeComplementLengthExponent]
  · dsimp only [routeTGapMomentNu]
    linarith [maynardLongGlobalAmplitudeDeficit_pos]

/-- The normalized two-alternative receiver is false on the exact `mu = 8` derivative seam.
The first branch fails even with no logarithmic power, while the second branch has negative height
exponent. -/
theorem not_routeT_muEight_derivativeSeam_twoAlternative
    (q : ℕ) {T : ℝ} (hT : 1 < T) (hlog : 1 ≤ Real.log T) :
    ¬ IsRouteTMaynardTwoAlternative q T T (T ^ (8 : ℝ)) (7 / 8 : ℝ) := by
  intro halt
  have hT0 : 0 < T := zero_lt_one.trans hT
  have htarget : (T ^ (8 : ℝ)) ^ (1 - (7 / 8 : ℝ)) = T := by
    rw [← Real.rpow_mul hT0.le]
    norm_num
  have hlogPow : 1 ≤ (Real.log T) ^ q := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog q
  have hfirstLarge : T ≤ T * (Real.log T) ^ q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlogPow hT0.le
  rcases halt with hfirst | hsecond
  · rw [htarget] at hfirst
    exact (not_lt_of_ge hfirstLarge) hfirst
  · have hexp : 1 + 8 *
        (1 + routeTGapMomentNu - 2 * (7 / 8 : ℝ)) < 0 :=
      routeT_muEight_derivativeSeam_classification.2.2.2
    have hheight := routeT_height_scale_identity
      hT.le (x := T ^ (8 : ℝ)) (mu := 8)
      (e := 1 + routeTGapMomentNu - 2 * (7 / 8 : ℝ)) rfl
    have hrhs : T * (T ^ (8 : ℝ)) ^
          (1 + routeTGapMomentNu - 2 * (7 / 8 : ℝ)) < 1 := by
      rw [hheight]
      exact Real.rpow_lt_one_of_one_lt_of_neg hT hexp
    linarith

end

end RHTower.Sieve
