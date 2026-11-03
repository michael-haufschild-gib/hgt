import GaloisForLFunctions.WindowTowerOfSpecZ.TheQuinticWindowHasExactLagData
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity
import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstPrimeWindowOddStrip
import GaloisForLFunctions.HTGeometry.HyperbolicBounds

/-!
# A negative direction of the retained Gamma lower form

The quintic window retains both lag corrections, the sinh pole and the signed
prime-two correlation. Their joint lower form is strictly negative. This tests
the discarded Gamma remainder, not the sign of the complete Weil form.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- The unit odd Gamma comparison with its prime-two and sinh terms retained. -/
def retainedOddGammaLowerForm (F : ℝ → ℝ) : ℝ :=
  (∫ t in Ioc (0 : ℝ) 1, ((∫ x, F x ^ 2) - autocorr F t) / t) -
    (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2) * (∫ x, F x ^ 2) -
    (∫ t in Ioc (0 : ℝ) 1, t * ((∫ x, F x ^ 2) - autocorr F t)) / 24 -
    (∫ x, x * F x) ^ 2 / 16 - sinhPairing F ^ 2 / 2 -
    2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2)

private def quinticCorrLower : ℝ :=
  let l : ℝ := 693147180 / 1000000000
  let h : ℝ := 693147181 / 1000000000
  62 / 1155 - 334 / 315 * h ^ 2 + 2 / 3 * l ^ 3 + 88 / 21 * l ^ 4 -
    86 / 15 * h ^ 5 + 268 / 105 * l ^ 7 - 16 / 21 * h ^ 9 + 64 / 693 * l ^ 11

private theorem quinticCorrLower_le : quinticCorrLower ≤ autocorr quinticWindow (Real.log 2) := by
  have hl : (693147180 / 1000000000 : ℝ) ≤ Real.log 2 := by
    linarith only [Real.log_two_gt_d9]
  have hu : Real.log 2 ≤ (693147181 / 1000000000 : ℝ) := by
    linarith only [Real.log_two_lt_d9]
  have hp : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 := pow_le_pow_left₀ hp hu 2
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147180 / 1000000000) hl 3
  have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147180 / 1000000000) hl 4
  have h5 := pow_le_pow_left₀ hp hu 5
  have h7 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147180 / 1000000000) hl 7
  have h9 := pow_le_pow_left₀ hp hu 9
  have h11 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147180 / 1000000000) hl 11
  change quinticCorrLower ≤ ∫ x, quinticWindow x * quinticWindow (x + Real.log 2)
  rw [quinticWindow_autocorr hp (by linarith only [hu])]
  unfold quinticCorrLower quinticCorrPoly
  dsimp only
  linarith only [h2, h3, h4, h5, h7, h9, h11]

private theorem quintic_prime_cost_le :
    -(2 * (Real.log 2 / Real.sqrt 2) * autocorr quinticWindow (Real.log 2)) ≤
      -2 * (4902 / 10000) * quinticCorrLower := by
  have hw := ArithmeticIncidencePositivity.vonMangoldtAtom_two_bounds
  simp only [vonMangoldtAtom, if_pos le_rfl,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat] at hw
  have hc0 : quinticCorrLower ≤ 0 := by norm_num [quinticCorrLower]
  have h1 := mul_le_mul_of_nonpos_left quinticCorrLower_le
    (show -(2 * (Real.log 2 / Real.sqrt 2)) ≤ 0 by linarith only [hw.1])
  have h2 := mul_le_mul_of_nonneg_right hw.2 (neg_nonneg.mpr hc0)
  nlinarith only [h1, h2]

private theorem quinticWindow_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ quinticWindow x := by
  by_cases hi : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · have hs : x ^ 2 ≤ 1 / 4 := by
      nlinarith only [mul_nonneg (by linarith only [hx] : 0 ≤ x + 1 / 2)
        (by linarith only [hi.2] : 0 ≤ 1 / 2 - x)]
    rw [quinticWindow, cubicWindow_inside hi.1 hi.2]
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hx (by linarith only [hs])))
      (by linarith only [hs])
  · rw [quinticWindow_outside hi]

private theorem quintic_pole_cost_ge : (121 / 88200 : ℝ) ≤ sinhPairing quinticWindow ^ 2 / 2 := by
  have hpos (x : ℝ) (hx : 0 ≤ x) :
      x * quinticWindow x ≤ quinticWindow x * (2 * Real.sinh (x / 2)) := by
    have h := HTGeometry.self_le_sinh_of_nonneg (by positivity : 0 ≤ x / 2)
    have hm := mul_le_mul_of_nonneg_right (show x ≤ 2 * Real.sinh (x / 2) by linarith only [h])
      (quinticWindow_nonneg hx)
    simpa only [mul_comm] using hm
  have hpt (x : ℝ) : x * quinticWindow x ≤ quinticWindow x * (2 * Real.sinh (x / 2)) := by
    by_cases hx : 0 ≤ x
    · exact hpos x hx
    · have h := hpos (-x) (by linarith only [not_le.mp hx])
      simpa only [quinticWindow_odd, neg_div, Real.sinh_neg, mul_neg, neg_mul, neg_neg] using h
  have hi1 : Integrable (fun x => x * quinticWindow x) :=
    (continuous_id.mul continuous_quinticWindow).integrable_of_hasCompactSupport
      compact_quinticWindow.mul_left
  have hi2 : Integrable (fun x => quinticWindow x * (2 * Real.sinh (x / 2))) :=
    (continuous_quinticWindow.mul (by fun_prop)).integrable_of_hasCompactSupport
      compact_quinticWindow.mul_right
  have h := integral_mono hi1 hi2 hpt
  rw [quinticWindow_position_moment] at h
  change (11 / 210 : ℝ) ≤ sinhPairing quinticWindow at h
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11 / 210) h 2
  norm_num at hs
  linarith only [hs]

private theorem gamma_constant_lower :
    577215 / 1000000 + 1098612 / 1000000 + 1 - 3 / (314159 / 100000) +
      693147180 / 1000000000 ≤
        Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 := by
  have hp : (314159 / 100000 : ℝ) < Real.pi := by
    linarith only [Real.pi_gt_d6]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 3 / Real.pi)
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) Real.pi_ne_zero] at hlog
  have hdiv : 3 / Real.pi ≤ 3 / (314159 / 100000 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    norm_num
    linarith only [hp]
  have he := SelectivePositivityAndThresholdLaws.eulerMascheroniConstant_gt_577215_div_1000000
  linarith only [hlog, hdiv, he, Real.log_three_gt_d9, Real.log_two_gt_d9]

private theorem quintic_retained_certificate :
    (167 / 315 - 2 / 9 - 22 / 21 + 86 / 75 - 268 / 735 + 16 / 189 - 64 / 7623 : ℝ) -
      (577215 / 1000000 + 1098612 / 1000000 + 1 - 3 / (314159 / 100000) +
        693147180 / 1000000000) * (62 / 1155) -
      (167 / 630 - 2 / 15 - 44 / 63 + 86 / 105 - 268 / 945 + 16 / 231 - 64 / 9009) / 24 -
      (11 / 210) ^ 2 / 16 - 121 / 88200 - 2 * (4902 / 10000) * quinticCorrLower < 0 := by
  norm_num [quinticCorrLower]

/-- Both exact lag corrections still leave a negative lower form on the odd quintic. -/
theorem retainedOddGammaLowerForm_quintic_neg : retainedOddGammaLowerForm quinticWindow < 0 := by
  have hL := quinticWindow_logarithmic_integral
  have hM := quinticWindow_jump_first_moment
  change (∫ t in Ioc (0 : ℝ) 1,
    ((∫ x, quinticWindow x ^ 2) - autocorr quinticWindow t) / t) = _ at hL
  change (∫ t in Ioc (0 : ℝ) 1,
    t * ((∫ x, quinticWindow x ^ 2) - autocorr quinticWindow t)) = _ at hM
  rw [retainedOddGammaLowerForm, hL, hM, quinticWindow_mass, quinticWindow_position_moment]
  linarith only [gamma_constant_lower, quintic_prime_cost_le, quintic_pole_cost_ge,
    quintic_retained_certificate]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedOddGammaLowerForm_quintic_neg
