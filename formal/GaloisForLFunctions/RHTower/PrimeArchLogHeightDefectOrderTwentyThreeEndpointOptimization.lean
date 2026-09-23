import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance

/-!
# Order-23 endpoint optimization and D2 threshold advance

The order-23 fourth reciprocal-trace argument originally rounded its squared-height endpoint down
to `431 / 2`. Direct optimization of the same exact atom polynomial permits the larger endpoint
`431349 / 2000`. Four FE--Schwarz copies still overspend the strict global source budget, so every
off-line Xi zero has squared ordinate at least this larger value.

The resulting verified-height band advances the unconditional pure-prime D2 threshold from
`141799 / 10000` to `141858 / 10000`. No numerical zero verification or native-decision
certificate is used.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Optimized squared-height endpoint allowed by the order-23 fourth-trace budget. -/
def xiOrderTwentyThreeOptimizedHeightSq : ℝ := 431349 / 2000

/-- Direct endpoint optimization of the order-23 fourth reciprocal-trace atom floor. -/
theorem seventeen_over_eightHundredThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyThree_optimized
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ))
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4)
    (hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ))
    (hvUpper : (q.1 : ℂ).im ^ (2 : ℕ) < xiOrderTwentyThreeOptimizedHeightSq) :
    (17 / 800000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  let w : ℝ := u + v
  let W : ℝ := 431849 / 2000
  have hu0 : 0 < u := by simpa only [u] using huLower
  have hv0 : 0 < v := by dsimp only [v]; linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hvLower
  have hvU : v < xiOrderTwentyThreeOptimizedHeightSq := by
    simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 2365 / 16 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by
    dsimp only [w, W, xiOrderTwentyThreeOptimizedHeightSq] at *
    linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ (2 : ℕ) < W ^ (2 : ℕ) :=
    (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsqLower : (2365 / 16 : ℝ) ^ (2 : ℕ) < w ^ (2 : ℕ) :=
    (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
  have hsecond : 0 < 17 * (W ^ (2 : ℕ) + w ^ (2 : ℕ)) - 800000 := by
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      800000 * W ^ (2 : ℕ) - 17 * W ^ (4 : ℕ) <
        800000 * w ^ (2 : ℕ) - 17 * w ^ (4 : ℕ) := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (800000 * w ^ (2 : ℕ) - 17 * w ^ (4 : ℕ)) -
            (800000 * W ^ (2 : ℕ) - 17 * W ^ (4 : ℕ)) =
          (W ^ (2 : ℕ) - w ^ (2 : ℕ)) * (17 * (W ^ (2 : ℕ) + w ^ (2 : ℕ)) - 800000) := by
      ring
    nlinarith
  have huv : u * v < xiOrderTwentyThreeOptimizedHeightSq / 4 := by
    calc
      u * v < (1 / 4 : ℝ) * v := mul_lt_mul_of_pos_right huU hv0
      _ < (1 / 4 : ℝ) * xiOrderTwentyThreeOptimizedHeightSq :=
        mul_lt_mul_of_pos_left hvU (by norm_num)
      _ = xiOrderTwentyThreeOptimizedHeightSq / 4 := by ring
  have hendpoint :
      6400000 * (xiOrderTwentyThreeOptimizedHeightSq / 4) <
        800000 * W ^ (2 : ℕ) - 17 * W ^ (4 : ℕ) := by
    norm_num [xiOrderTwentyThreeOptimizedHeightSq, W]
  have huvScaled :
      6400000 * (u * v) <
        6400000 * (xiOrderTwentyThreeOptimizedHeightSq / 4) :=
    mul_lt_mul_of_pos_left huv (by norm_num)
  have hchain :
      6400000 * (u * v) < 800000 * w ^ (2 : ℕ) - 17 * w ^ (4 : ℕ) :=
    huvScaled.trans (hendpoint.trans hshape)
  have hG :
      0 < 800000 * (v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ)) - 17 * w ^ (4 : ℕ) := by
    have hN : v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ) = w ^ (2 : ℕ) - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hN]
    nlinarith [hchain]
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re =
        (v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ)) / w ^ (4 : ℕ) := by
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 800000) (pow_pos hw0 4)]
  nlinarith

/-- Optimized order-23 source budget excludes every off-line Xi zero below the new endpoint. -/
theorem xiZeroCopy_re_eq_half_of_im_sq_lt_orderTwentyThreeOptimized
    (q : XiZeroCopy)
    (hheight : (q.1 : ℂ).im ^ (2 : ℕ) < xiOrderTwentyThreeOptimizedHeightSq) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hoff
  by_cases hlow : (q.1 : ℂ).im ^ (2 : ℕ) < 2365 / 16
  · exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hlow)
  · have hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ) := le_of_not_gt hlow
    have huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hoff)
    have huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 :=
      xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hatom :=
      seventeen_over_eightHundredThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyThree_optimized
        q huLower huUpper hvLower hheight
    have hquartet := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hoff
    have hsource := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
    nlinarith

/-- Equivalent optimized positive height gap for every off-line Xi copy. -/
theorem orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiOrderTwentyThreeOptimizedHeightSq ≤ (q.1 : ℂ).im ^ (2 : ℕ) := by
  exact le_of_not_gt fun hheight =>
    hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_orderTwentyThreeOptimized q hheight)

/-- Optimized order-23 height exclusion exposed as a verified-height certificate. -/
theorem rhVerifiedThrough_of_sq_lt_orderTwentyThreeOptimized
    (H : ℝ) (hHsq : H ^ (2 : ℕ) < xiOrderTwentyThreeOptimizedHeightSq) :
    RHVerifiedThrough H := by
  intro rho hzero _hre0 _hre1 him0 himUpper
  let rhoSupport : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rhoSupport
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by
      omega
    exact ⟨rhoSupport, ⟨0, hn⟩⟩
  have hsq : (q.1 : ℂ).im ^ (2 : ℕ) < xiOrderTwentyThreeOptimizedHeightSq := by
    change rho.im ^ (2 : ℕ) < xiOrderTwentyThreeOptimizedHeightSq
    nlinarith
  have hline :=
    xiZeroCopy_re_eq_half_of_im_sq_lt_orderTwentyThreeOptimized q hsq
  simpa only [q, rhoSupport] using hline

/-- Near-maximal rational D2 threshold below the optimized order-23 endpoint. -/
def xiOrderTwentyThreeOptimizedD2Threshold : ℝ := 141858 / 10000

/-- The optimized D2 threshold strictly improves the earlier order-23 threshold. -/
theorem xiOrderTwentyThreeD2Threshold_lt_optimized :
    xiOrderTwentyThreeD2Threshold < xiOrderTwentyThreeOptimizedD2Threshold := by
  norm_num [xiOrderTwentyThreeD2Threshold, xiOrderTwentyThreeOptimizedD2Threshold]

/-- Exact verified-height certificate used by the optimized D2 threshold. -/
theorem rhVerifiedThrough_xiOrderTwentyThreeOptimizedD2Threshold_add_half :
    RHVerifiedThrough (xiOrderTwentyThreeOptimizedD2Threshold + 1 / 2) := by
  apply rhVerifiedThrough_of_sq_lt_orderTwentyThreeOptimized
  norm_num [xiOrderTwentyThreeOptimizedD2Threshold,
    xiOrderTwentyThreeOptimizedHeightSq]

/-- Explicit pure-prime floor on the extra optimized order-23 band. -/
theorem primeArchLogHeightDefect_lower_of_orderTwentyThreeOptimizedBand
    {s : ℂ} (hsRe : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hsLow : 233 / 20 < s.im)
    (hsUpper : s.im ≤ xiOrderTwentyThreeOptimizedD2Threshold) :
    -(Real.log Real.pi + Real.log 2) - 8 ≤ primeArchLogHeightDefect s := by
  exact primeArchLogHeightDefect_lower_of_verifiedHeightBand
    (xiOrderTwentyThreeOptimizedD2Threshold + 1 / 2)
    xiOrderTwentyThreeOptimizedD2Threshold
    rhVerifiedThrough_xiOrderTwentyThreeOptimizedD2Threshold_add_half
    (by linarith) hsRe hsHalf hsLow hsUpper

/-- Premise-free optimized order-23 D2 endpoint. -/
theorem primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_xiOrderTwentyThreeOptimizedThreshold_iff_rh :
    PrimeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow
        xiOrderTwentyThreeOptimizedD2Threshold ↔ RiemannHypothesis := by
  exact
    primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_iff_rh_of_verifiedHeightBand
      (xiOrderTwentyThreeOptimizedD2Threshold + 1 / 2)
      xiOrderTwentyThreeOptimizedD2Threshold
      rhVerifiedThrough_xiOrderTwentyThreeOptimizedD2Threshold_add_half
      (by linarith)
      (by norm_num [xiOrderTwentyThreeOptimizedD2Threshold])

end

end RHTower
