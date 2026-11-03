import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaComparisonRetainsItsLagMoments
import GaloisForLFunctions.WindowTowerOfSpecZ.TheRetainedGammaLowerFormHasANegativeDirection
import GaloisForLFunctions.WindowTowerOfSpecZ.TheExitChargePaysEveryNewFold
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A positive reserve in the exterior Gamma tail

The first three positive Laplace modes already improve the unit Gamma tail
by `1/128`. Retaining that tail in the lag comparison yields `E/64` beyond
the lower form containing both lag moments, the signed prime and the pole.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole

namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticIncidencePositivity ArithmeticCriticalityTheory
open BiScaleUncertainty LatticeSectionTheory SpacingScaleHarmonicAnalysis

private theorem exp_neg_half_gt : (20 / 33 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
  have he : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hp := Real.exp_pos (1 / 2 : ℝ)
  have hu : Real.exp (1 / 2 : ℝ) < 33 / 20 := by
    nlinarith only [he, Real.exp_one_lt_d9, hp]
  rw [Real.exp_neg, ← one_div]
  exact (lt_div_iff₀ hp).mpr (by linarith only [hu])

private theorem gamma_three_modes_le {t : ℝ} (ht : 0 < t) :
    Real.exp (-(1 / 2 : ℝ) * t) + Real.exp (-(5 / 2 : ℝ) * t) +
      Real.exp (-(9 / 2 : ℝ) * t) ≤ archLevyDensity t := by
  have h := Summable.sum_le_tsum (Finset.range 3)
    (fun n _ => (Real.exp_pos (-(2 * (n : ℝ) + 1 / 2) * t)).le)
    (hasSum_archLevyDensity ht).summable
  rw [← archLevyDensity_eq_tsum ht] at h
  norm_num [Finset.sum_range_succ] at h
  exact h

/-- Three positive exponential modes give a lower bound for the exact exterior tail. -/
theorem gamma_tail_one_three_modes :
    2 * (Real.exp (-(1 / 2 : ℝ)) + Real.exp (-(1 / 2 : ℝ)) ^ 5 / 5 +
      Real.exp (-(1 / 2 : ℝ)) ^ 9 / 9) ≤ archLevyAntideriv 1 := by
  have h0 := integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 1
  have h1 := integrableOn_exp_mul_Ioi (by norm_num : -(5 / 2 : ℝ) < 0) 1
  have h2 := integrableOn_exp_mul_Ioi (by norm_num : -(9 / 2 : ℝ) < 0) 1
  have hw := WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi
    (by norm_num : (0 : ℝ) < 1)
  have h := setIntegral_mono_on ((h0.add h1).add h2) hw measurableSet_Ioi
    (fun t ht => gamma_three_modes_le (lt_trans zero_lt_one ht))
  simp only [Pi.add_apply] at h
  rw [integral_add (h0.add h1) h2, integral_add h0 h1,
    integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0),
    integral_exp_mul_Ioi (by norm_num : -(5 / 2 : ℝ) < 0),
    integral_exp_mul_Ioi (by norm_num : -(9 / 2 : ℝ) < 0),
    WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 1)] at h
  have he5 : Real.exp (-(5 / 2 : ℝ)) = Real.exp (-(1 / 2 : ℝ)) ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he9 : Real.exp (-(9 / 2 : ℝ)) = Real.exp (-(1 / 2 : ℝ)) ^ 9 := by
    rw [← Real.exp_nat_mul]
    norm_num
  simp only [mul_one, he5, he9] at h
  linarith only [h]

/-- The exterior tail alone retains more than `1/128` beyond the quadratic comparison. -/
theorem gamma_tail_one_reserve :
    (1 / 128 : ℝ) < archLevyAntideriv 1 - Real.log 2 - Real.pi / 4 + 1 / 4 - 1 / 96 := by
  have he := exp_neg_half_gt
  have he5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20 / 33) he.le 5
  have he9 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20 / 33) he.le 9
  have hc : Real.log 2 + Real.pi / 4 - 1 / 4 + 1 / 96 + 1 / 128 <
      2 * ((20 / 33 : ℝ) + (20 / 33 : ℝ)^5 / 5 + (20 / 33 : ℝ)^9 / 9) := by
    have hl := Real.log_two_lt_d9
    have hp := Real.pi_lt_d4
    norm_num at hl hp ⊢
    linarith only [hl, hp]
  linarith only [gamma_tail_one_three_modes, hc, he, he5, he9]

/-- The retained lag form gains `E/64` from the exterior Gamma reserve. -/
theorem unit_odd_gamma_position_reserve {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) -
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2) * (∫ x, F x ^ 2) -
      (∫ t in Ioc (0 : ℝ) 1, t * (autocorr F 0 - autocorr F t)) / 24 -
      (∫ x, x * F x) ^ 2 / 16 + (∫ x, F x ^ 2) / 64 ≤
        EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  have h := unit_odd_gamma_lag_moments_with_tail_lower hF hcs hs ho
  rw [unit_odd_jump_second_moment hF hcs hs ho] at h
  simp only [autocorr_zero_eq] at h ⊢
  have hE : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hr := mul_le_mul_of_nonneg_right gamma_tail_one_reserve.le hE
  nlinarith only [h, hr]

/-- The complete unit-window form exceeds the retained Gamma/prime/pole form by `E/64`. -/
theorem weilQuad_ge_retainedOddGamma_add_reserve {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    retainedOddGammaLowerForm F + (∫ x, F x ^ 2) / 64 ≤ weilQuad F := by
  have hcs : HasCompactSupport F :=
    HasCompactSupport.intro isCompact_Icc
      (fun x hx => image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht))
  have hN : ∀ n : ℕ, 2 < n → ∀ u, F u * F (u + Real.log n) = 0 := by
    intro n hn u
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    have hlog : 1 < Real.log n :=
      lt_of_lt_of_le (by linarith only [Real.log_three_gt_d9])
        (Real.log_le_log (by norm_num) hn3)
    by_cases hu : F u = 0
    · rw [hu, zero_mul]
    · have huI : u ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        by_contra hnot
        exact hu (image_eq_zero_of_notMem_tsupport fun h => hnot (hs h))
      have hz : F (u + Real.log n) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        have hbound := (hs h).2
        linarith only [huI.1, hlog, hbound]
      rw [hz, mul_zero]
  have hfull := weil_eq_markovForm_add_pole hF hcs hN
  have hstep := markovForm_succ hF.continuous hcs (N := 1) le_rfl
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hstep
  have hbase : markovForm 1 F = EF.gammaBracket 0 * (∫ x, F x ^ 2) +
      biScaleLevyEnergy F := by
    norm_num [markovForm, creationPotential, primeJump]
    rw [levyJump_eq_biScale hF hcs]
    ring
  have hw : primeJumpWeight 2 = Real.log 2 / Real.sqrt 2 := by
    unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hgamma := unit_odd_gamma_position_reserve hF hcs hs ho
  simp only [autocorr_zero_eq] at hgamma
  change markovForm 2 F = markovForm 1 F -
    2 * primeJumpWeight 2 * autocorr F (Real.log 2) at hstep
  rw [hbase, hw] at hstep
  change weilQuad F = markovForm 2 F + coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2 at hfull
  unfold retainedOddGammaLowerForm
  nlinarith only [hgamma, hstep, hfull, sq_nonneg (coshPairing F)]

private def quinticCorrUpper : ℝ :=
  let l : ℝ := 693147180 / 1000000000
  let h : ℝ := 693147181 / 1000000000
  62 / 1155 - 334 / 315 * l ^ 2 + 2 / 3 * h ^ 3 + 88 / 21 * h ^ 4 -
    86 / 15 * l ^ 5 + 268 / 105 * h ^ 7 - 16 / 21 * l ^ 9 + 64 / 693 * h ^ 11

private theorem quinticCorr_le_upper : autocorr quinticWindow (Real.log 2) ≤ quinticCorrUpper := by
  have hl : (693147180 / 1000000000 : ℝ) ≤ Real.log 2 := by
    linarith only [Real.log_two_gt_d9]
  have hu : Real.log 2 ≤ (693147181 / 1000000000 : ℝ) := by
    linarith only [Real.log_two_lt_d9]
  have hp : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147180 / 1000000000) hl 2
  have h3 := pow_le_pow_left₀ hp hu 3
  have h4 := pow_le_pow_left₀ hp hu 4
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147180 / 1000000000) hl 5
  have h7 := pow_le_pow_left₀ hp hu 7
  have h9 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147180 / 1000000000) hl 9
  have h11 := pow_le_pow_left₀ hp hu 11
  change (∫ x, quinticWindow x * quinticWindow (x + Real.log 2)) ≤ _
  rw [quinticWindow_autocorr hp (by linarith only [hu])]
  unfold quinticCorrUpper quinticCorrPoly
  dsimp only
  linarith only [h2, h3, h4, h5, h7, h9, h11]

private theorem quintic_prime_gain_ge :
    -(2 * (49 / 100 : ℝ)) * quinticCorrUpper ≤
      -(2 * (Real.log 2 / Real.sqrt 2)) * autocorr quinticWindow (Real.log 2) := by
  have hs : Real.sqrt 2 ≤ 14143 / 10000 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hw : (49 / 100 : ℝ) ≤ Real.log 2 / Real.sqrt 2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith only [hs, Real.log_two_gt_d9]
  have hc0 : quinticCorrUpper ≤ 0 := by norm_num [quinticCorrUpper]
  have h1 := mul_le_mul_of_nonpos_left quinticCorr_le_upper
    (show -(2 * (Real.log 2 / Real.sqrt 2)) ≤ 0 by linarith only [hw])
  have h2 := mul_le_mul_of_nonneg_right hw (neg_nonneg.mpr hc0)
  nlinarith only [h1, h2]

private theorem cosh_quarter_square_bound : Real.cosh (1 / 4 : ℝ) ^ 2 ≤ 16 / 15 := by
  have hc := pow_le_pow_left₀ (Real.cosh_pos (1 / 4 : ℝ)).le
    (Real.cosh_le_exp_half_sq (1 / 4 : ℝ)) 2
  rw [← Real.exp_nat_mul] at hc
  norm_num at hc
  have he : Real.exp (1 / 16 : ℝ) * Real.exp (-(1 / 16 : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hl : (15 / 16 : ℝ) ≤ Real.exp (-(1 / 16 : ℝ)) := by
    linarith only [Real.add_one_le_exp (-(1 / 16 : ℝ))]
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_pos (1 / 16 : ℝ)).le
  linarith only [hc, he, hm]

private theorem quintic_pole_cost_le :
    sinhPairing quinticWindow ^ 2 / 2 ≤ (8 / 15 : ℝ) * (11 / 210) ^ 2 := by
  have hI : Integrable (fun x : ℝ => Real.cosh (1 / 4 : ℝ) * (x * quinticWindow x)) :=
    ((continuous_const.mul (continuous_id.mul continuous_quinticWindow)).integrable_of_hasCompactSupport
      compact_quinticWindow.mul_left.mul_left)
  have hb : ∀ x : ℝ, ‖quinticWindow x * (2 * Real.sinh (x / 2))‖ ≤
      Real.cosh (1 / 4 : ℝ) * (x * quinticWindow x) := by
    intro x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · have hxa : |x| ≤ 1 / 2 := abs_le.mpr hx
      have hcosh : Real.cosh (|x| / 2) ≤ Real.cosh (1 / 4 : ℝ) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : 0 ≤ |x| / 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        linarith only [hxa]
      have hs : |Real.sinh (x / 2)| ≤ |x| / 2 * Real.cosh (1 / 4 : ℝ) := by
        rw [Real.abs_sinh, abs_div, abs_two]
        exact (sinh_le_mul_cosh (by positivity)).trans
          (mul_le_mul_of_nonneg_left hcosh (by positivity))
      have hx2 : x ^ 2 ≤ 1 / 4 := by
        have h := pow_le_pow_left₀ (abs_nonneg x) hxa 2
        simpa only [sq_abs] using h
      have hnonneg : 0 ≤ x * quinticWindow x := by
        rw [quinticWindow, cubicWindow]
        have he : x * (2 * (x * max (1 - 4 * x ^ 2) 0) * (1 - 2 * x ^ 2)) =
            2 * x ^ 2 * max (1 - 4 * x ^ 2) 0 * (1 - 2 * x ^ 2) := by ring
        rw [he]
        exact mul_nonneg (by positivity) (by linarith only [hx2])
      have hxf : |quinticWindow x| * |x| = x * quinticWindow x := by
        rw [← abs_mul, mul_comm (quinticWindow x) x, abs_of_nonneg hnonneg]
      calc ‖quinticWindow x * (2 * Real.sinh (x / 2))‖
          = (2 * |quinticWindow x|) * |Real.sinh (x / 2)| := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
              ring
        _ ≤ (2 * |quinticWindow x|) * (|x| / 2 * Real.cosh (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = Real.cosh (1 / 4 : ℝ) * (|quinticWindow x| * |x|) := by ring
        _ = Real.cosh (1 / 4 : ℝ) * (x * quinticWindow x) := by rw [hxf]
    · rw [quinticWindow_outside hx]
      simp
  have hN := norm_integral_le_of_norm_le hI (Eventually.of_forall hb)
  rw [integral_const_mul, quinticWindow_position_moment, Real.norm_eq_abs] at hN
  change |sinhPairing quinticWindow| ≤ Real.cosh (1 / 4 : ℝ) * (11 / 210) at hN
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hN 2
  rw [sq_abs, mul_pow] at hsq
  norm_num at hsq
  nlinarith only [hsq, cosh_quarter_square_bound]

private theorem gamma_constant_upper :
    Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 ≤
      577216 / 1000000 + 1098613 / 1000000 + 31416 / 30000 - 1 +
        693147181 / 1000000000 := by
  have hu : Real.log Real.pi ≤ Real.log 3 + Real.pi / 3 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
    rw [Real.log_div Real.pi_ne_zero (by norm_num)] at h
    linarith only [h]
  have hg := _root_.RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith only [hu, hg, Real.log_three_lt_d9, Real.pi_lt_d4, Real.log_two_lt_d9]

private theorem quintic_reserve_certificate :
    0 < (167 / 315 - 2 / 9 - 22 / 21 + 86 / 75 - 268 / 735 + 16 / 189 - 64 / 7623 : ℝ) -
      (577216 / 1000000 + 1098613 / 1000000 + 31416 / 30000 - 1 +
        693147181 / 1000000000) * (62 / 1155) -
      (167 / 630 - 2 / 15 - 44 / 63 + 86 / 105 - 268 / 945 + 16 / 231 - 64 / 9009) / 24 -
      (11 / 210) ^ 2 / 16 - (8 / 15) * (11 / 210) ^ 2 -
      2 * (49 / 100) * quinticCorrUpper + (62 / 1155) / 64 := by
  norm_num [quinticCorrUpper]

/-- The exterior reserve is large enough to repair the explicit negative quintic direction. -/
theorem retainedOddGammaLowerForm_quintic_add_reserve_pos :
    0 < retainedOddGammaLowerForm quinticWindow + (∫ x, quinticWindow x ^ 2) / 64 := by
  have hL := quinticWindow_logarithmic_integral
  have hM := quinticWindow_jump_first_moment
  change (∫ t in Ioc (0 : ℝ) 1,
    ((∫ x, quinticWindow x ^ 2) - autocorr quinticWindow t) / t) = _ at hL
  change (∫ t in Ioc (0 : ℝ) 1,
    t * ((∫ x, quinticWindow x ^ 2) - autocorr quinticWindow t)) = _ at hM
  rw [retainedOddGammaLowerForm, hL, hM, quinticWindow_mass, quinticWindow_position_moment]
  linarith only [gamma_constant_upper, quintic_prime_gain_ge, quintic_pole_cost_le,
    quintic_reserve_certificate]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_tail_one_reserve
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_odd_gamma_position_reserve
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_retainedOddGamma_add_reserve
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedOddGammaLowerForm_quintic_add_reserve_pos
