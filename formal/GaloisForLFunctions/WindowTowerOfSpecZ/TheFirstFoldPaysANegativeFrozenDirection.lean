import GaloisForLFunctions.WindowTowerOfSpecZ.TheCubicWindowHasExactJumpMoments
import GaloisForLFunctions.WindowTowerOfSpecZ.TheExitChargePaysEveryNewFold
import GaloisForLFunctions.BiScaleUncertainty.CompactAutocorrelationPolarMoment
import GaloisForLFunctions.ArithmeticIncidencePositivity.SecondOrderSurplusPotential
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit
import GaloisForLFunctions.«arithmetic-positivity-theory».MarkovPoleHyperbolicCapacityAndApertureThresholds

/-!
# A negative frozen direction at the first prime fold

The odd cubic on a unit window has frozen archimedean energy below
`−29/2100` times its mass, while its complete Weil energy exceeds `1/100`
times its mass. Exact correlation moments bound the Gamma jump integral;
the negative correlation at `log 2` supplies the positive prime contribution.

Mollification preserves both strict signs. A translation gives a C² test
in `[-21/20,0]` with `Q₁ < 0 < Q`, disproving the first-stage collar loan
while retaining the signed fold as the source of positivity.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open scoped CompactlySupported
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole

namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticIncidencePositivity ArithmeticPositivityTheory ArithmeticCriticalityTheory BiScaleUncertainty
open SpacingScaleHarmonicAnalysis BiScaleUncertainty.SignedPrimePolar

/-- A rational enclosure of the negative constant in the Gamma form. -/
private theorem gamma_origin_bounds :
    -(269 / 50 : ℝ) < EF.gammaBracket 0 ∧ EF.gammaBracket 0 < -(26 / 5) := by
  have he := neg_gammaBracket_zero_eq
  have hl : Real.log 3 ≤ Real.log Real.pi :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_d4])
  have hu : Real.log Real.pi ≤ Real.log 3 + Real.pi / 3 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
    rw [Real.log_div Real.pi_ne_zero (by norm_num)] at h
    linarith only [h]
  have hg := _root_.RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  constructor
  · linarith only [he, hu, Real.log_two_lt_d9, Real.log_three_lt_d9, hg, Real.pi_lt_d4]
  · linarith only [he, hl, Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.one_half_lt_eulerMascheroniConstant, Real.pi_gt_d4]

/-- A tail enclosure at the unit support length. -/
private theorem gamma_tail_one_bounds :
    Real.log 2 + Real.pi / 4 - 1 / 4 + 1 / 96 ≤ archLevyAntideriv 1 ∧
      archLevyAntideriv 1 ≤ 251 / 200 := by
  have hlog : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = (2 ^ (2 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  constructor
  · have h := archLevyAntideriv_ge_second (y := 1) (by norm_num) (by norm_num)
    rw [hlog] at h
    norm_num at h
    linarith only [h]
  · have h := archLevyAntideriv_le_expansion (y := 1) (by norm_num)
    rw [hlog] at h
    norm_num at h
    linarith only [h, Real.log_two_lt_d9, Real.pi_lt_d4]

private theorem cubic_autocorr_zero : autocorr cubicWindow 0 = 2 / 105 := by
  simpa [autocorr, cubicCorrPoly] using cubicWindow_autocorr (t := 0) le_rfl (by norm_num)

private theorem cubic_deficit_nonneg (t : ℝ) : 0 ≤ 2 / 105 - autocorr cubicWindow t := by
  have h := integral_sub_shift_sq compact_cubicWindow continuous_cubicWindow t
  rw [cubic_autocorr_zero] at h
  have hn : 0 ≤ ∫ x, (cubicWindow x - cubicWindow (x + t)) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  linarith only [h, hn]

private theorem cubic_deficit_poly_nonneg {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ 2 / 105 - cubicCorrPoly t := by
  rw [← cubicWindow_autocorr ht.1.le ht.2]
  exact cubic_deficit_nonneg t

private def cubicJumpIntegrand (t : ℝ) : ℝ :=
  (2 / 105 - autocorr cubicWindow t) * archLevySinhWeight t

private theorem cubicJumpIntegrand_eq {t : ℝ} (ht : 0 < t) :
    cubicJumpIntegrand t = (2 / 105 - autocorr cubicWindow t) * (2 * archLevyDensity t) := by
  rw [cubicJumpIntegrand, archLevySinhWeight, exp_half_div_sinh_eq ht]

private theorem cubicJumpIntegrand_tail {t : ℝ} (ht : 1 < t) :
    cubicJumpIntegrand t = 2 / 105 * (2 * archLevyDensity t) := by
  rw [cubicJumpIntegrand_eq (by linarith only [ht])]
  change (2 / 105 - (∫ x, cubicWindow x * cubicWindow (x + t))) * _ = _
  rw [cubicWindow_autocorr_tail ht, sub_zero]

private theorem cubicJumpIntegrand_le {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    cubicJumpIntegrand t ≤ (2 / 105 - cubicCorrPoly t) / t +
      (2 / 105 - cubicCorrPoly t) / 2 := by
  have hac : autocorr cubicWindow t = cubicCorrPoly t := cubicWindow_autocorr ht.1.le ht.2
  rw [cubicJumpIntegrand_eq ht.1, hac]
  have h := mul_le_mul_of_nonneg_left (archLevyDensity_le_inv ht.1)
    (show 0 ≤ 2 * (2 / 105 - cubicCorrPoly t) by
      exact mul_nonneg (by norm_num) (cubic_deficit_poly_nonneg ht))
  have he : 2 * (2 / 105 - cubicCorrPoly t) * (1 / (2 * t) + 1 / 4) =
      (2 / 105 - cubicCorrPoly t) / t + (2 / 105 - cubicCorrPoly t) / 2 := by
    field_simp [ht.1.ne']
    ring
  rw [he] at h
  calc (2 / 105 - cubicCorrPoly t) * (2 * archLevyDensity t)
      = 2 * (2 / 105 - cubicCorrPoly t) * archLevyDensity t := by ring
    _ ≤ _ := h

private theorem cubicJumpIntegrand_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ cubicJumpIntegrand t := by
  rw [cubicJumpIntegrand_eq ht]
  exact mul_nonneg (cubic_deficit_nonneg t)
    (mul_nonneg (by norm_num) (archLevyDensity_pos ht).le)

private theorem integrable_cubicJump_inner : IntegrableOn cubicJumpIntegrand (Ioc (0 : ℝ) 1) := by
  have hD : Continuous (fun t : ℝ => 2 / 105 - cubicCorrPoly t) := by
    unfold cubicCorrPoly
    fun_prop
  have hDI : IntegrableOn (fun t : ℝ => 2 / 105 - cubicCorrPoly t) (Ioc (0 : ℝ) 1) :=
    hD.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable cubicJumpIntegrand (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have hw := continuousOn_archLevySinhWeight_pos_halfLine.mono
      (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ ht => ht.1)
    refine ((hD.continuousOn.mul hw).aestronglyMeasurable measurableSet_Ioc).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hac : autocorr cubicWindow t = cubicCorrPoly t := cubicWindow_autocorr ht.1.le ht.2
    simp only [Pi.mul_apply, cubicJumpIntegrand, hac]
  apply (integrableOn_cubicWindow_logarithmic_deficit.add (hDI.div_const 2)).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (cubicJumpIntegrand_nonneg ht.1)]
  exact cubicJumpIntegrand_le ht

private theorem integrable_cubicJump_tail : IntegrableOn cubicJumpIntegrand (Ioi (1 : ℝ)) := by
  have hI : IntegrableOn (fun t : ℝ => (2 / 105 * 2) * archLevyDensity t) (Ioi (1 : ℝ)) :=
    (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 1)).const_mul _
  refine hI.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [cubicJumpIntegrand_tail ht]
  ring

private theorem integrable_cubicJump : IntegrableOn cubicJumpIntegrand (Ioi (0 : ℝ)) := by
  have h := integrable_cubicJump_inner.union integrable_cubicJump_tail
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at h

private theorem cubic_deficit_integral :
    (∫ t in Ioc (0 : ℝ) 1, 2 / 105 - cubicCorrPoly t) = 2 / 105 := by
  have hc : Continuous cubicCorrPoly := by unfold cubicCorrPoly; fun_prop
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_cubicCorrPoly]
  norm_num

private theorem cubicJump_inner_le :
    (∫ t in Ioc (0 : ℝ) 1, cubicJumpIntegrand t) ≤ (457 / 210 + 1 / 2) * (2 / 105) := by
  have hD : Continuous (fun t : ℝ => 2 / 105 - cubicCorrPoly t) := by
    unfold cubicCorrPoly
    fun_prop
  have hDI : IntegrableOn (fun t : ℝ => 2 / 105 - cubicCorrPoly t) (Ioc (0 : ℝ) 1) :=
    hD.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h := setIntegral_mono_on integrable_cubicJump_inner
    (integrableOn_cubicWindow_logarithmic_deficit.add (hDI.div_const 2))
    measurableSet_Ioc (fun t ht => cubicJumpIntegrand_le ht)
  simp only [Pi.add_apply] at h
  rw [integral_add integrableOn_cubicWindow_logarithmic_deficit (hDI.div_const 2),
    integral_div, cubicWindow_logarithmic_integral, cubic_deficit_integral] at h
  linarith only [h]

private theorem cubicJump_tail_integral :
    (∫ t in Ioi (1 : ℝ), cubicJumpIntegrand t) = 2 * archLevyAntideriv 1 * (2 / 105) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => cubicJumpIntegrand_tail ht),
    integral_const_mul, integral_const_mul,
    WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 1)]
  ring

private theorem cubic_gamma_jump_split :
    biScaleLevyEnergy cubicWindow = (∫ t in Ioc (0 : ℝ) 1, cubicJumpIntegrand t) +
      2 * archLevyAntideriv 1 * (2 / 105) := by
  unfold biScaleLevyEnergy
  rw [cubic_autocorr_zero]
  change (∫ t in Ioi (0 : ℝ), cubicJumpIntegrand t) = _
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      integrable_cubicJump_inner integrable_cubicJump_tail, cubicJump_tail_integral]

/-- The cubic's frozen archimedean form is strictly negative, before the pole term. -/
theorem cubicWindow_frozen_archimedean_neg :
    EF.gammaBracket 0 * (∫ x, cubicWindow x ^ 2) + biScaleLevyEnergy cubicWindow <
      -(29 / 2100 : ℝ) * (∫ x, cubicWindow x ^ 2) := by
  rw [cubicWindow_mass, cubic_gamma_jump_split]
  have hg := gamma_origin_bounds.2
  have ht := gamma_tail_one_bounds.2
  have hj := cubicJump_inner_le
  linarith only [hg, ht, hj]

private theorem cubicJumpIntegrand_ge {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    (2 / 105 - cubicCorrPoly t) / t + (2 / 105 - cubicCorrPoly t) / 2 -
      t * (2 / 105 - cubicCorrPoly t) / 24 - t ^ 2 * (2 / 105 - cubicCorrPoly t) / 16 ≤
        cubicJumpIntegrand t := by
  have hac : autocorr cubicWindow t = cubicCorrPoly t := cubicWindow_autocorr ht.1.le ht.2
  have h := mul_le_mul_of_nonneg_left (mul_archLevyDensity_ge_sharp ht.1 ht.2)
    (show 0 ≤ 2 * (2 / 105 - cubicCorrPoly t) by
      exact mul_nonneg (by norm_num) (cubic_deficit_poly_nonneg ht))
  refine le_of_mul_le_mul_left (a := t) ?_ ht.1
  have he : t * ((2 / 105 - cubicCorrPoly t) / t + (2 / 105 - cubicCorrPoly t) / 2 -
      t * (2 / 105 - cubicCorrPoly t) / 24 - t ^ 2 * (2 / 105 - cubicCorrPoly t) / 16) =
      2 * (2 / 105 - cubicCorrPoly t) * (1 / 2 + t / 4 - t ^ 2 / 48 - t ^ 3 / 32) := by
    field_simp [ht.1.ne']
    ring
  rw [he, cubicJumpIntegrand_eq ht.1, hac]
  calc _ ≤ 2 * (2 / 105 - cubicCorrPoly t) * (t * archLevyDensity t) := h
    _ = _ := by ring

private theorem cubicJump_inner_ge :
    (457 / 210 + 1 / 2 - 7 / 288 - 47 / 1920) * (2 / 105) ≤
      ∫ t in Ioc (0 : ℝ) 1, cubicJumpIntegrand t := by
  have hD : Continuous (fun t : ℝ => 2 / 105 - cubicCorrPoly t) := by
    unfold cubicCorrPoly
    fun_prop
  have hDI : IntegrableOn (fun t : ℝ => 2 / 105 - cubicCorrPoly t) (Ioc (0 : ℝ) 1) :=
    hD.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hTI : IntegrableOn (fun t : ℝ => t * (2 / 105 - cubicCorrPoly t)) (Ioc (0 : ℝ) 1) :=
    (continuous_id.mul hD).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hT2I : IntegrableOn (fun t : ℝ => t ^ 2 * (2 / 105 - cubicCorrPoly t)) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 2).mul hD).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hsum : IntegrableOn (fun t : ℝ => (2 / 105 - cubicCorrPoly t) / t +
      (2 / 105 - cubicCorrPoly t) / 2) (Ioc (0 : ℝ) 1) :=
    integrableOn_cubicWindow_logarithmic_deficit.add (hDI.div_const 2)
  have hsub : IntegrableOn (fun t : ℝ => (2 / 105 - cubicCorrPoly t) / t +
      (2 / 105 - cubicCorrPoly t) / 2 - t * (2 / 105 - cubicCorrPoly t) / 24)
      (Ioc (0 : ℝ) 1) := hsum.sub (hTI.div_const 24)
  have h := setIntegral_mono_on (hsub.sub (hT2I.div_const 16)) integrable_cubicJump_inner
    measurableSet_Ioc (fun t ht => cubicJumpIntegrand_ge ht)
  simp only [Pi.sub_apply] at h
  have hm1 := cubicWindow_jump_first_moment
  have hm2 := cubicWindow_jump_second_moment
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hm1 hm2
  rw [integral_sub hsub (hT2I.div_const 16), integral_sub hsum (hTI.div_const 24),
    integral_add integrableOn_cubicWindow_logarithmic_deficit (hDI.div_const 2),
    integral_div, integral_div, integral_div, cubicWindow_logarithmic_integral,
    cubic_deficit_integral, hm1, hm2] at h
  linarith only [h]

private theorem cubicWindow_position_moment :
    (∫ x, x * cubicWindow x) = 1 / 30 := by
  have he : (fun x => x * cubicWindow x) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun x => x ^ 2 - 4 * x ^ 4) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · rw [indicator_of_mem hx, cubicWindow_inside hx.1 hx.2]
      ring
    · rw [indicator_of_notMem hx, cubicWindow_outside hx, mul_zero]
  have hderiv (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 3 / 3 - 4 * x ^ 5 / 5)
      (x ^ 2 - 4 * x ^ 4) x := by
    have h1 := (hasDerivAt_pow 3 x).div_const 3
    have h2 := ((hasDerivAt_pow 5 x).const_mul 4).div_const 5
    exact (h1.sub h2).congr_deriv (by ring)
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      ((by fun_prop : Continuous (fun x : ℝ => x ^ 2 - 4 * x ^ 4)).intervalIntegrable _ _)]
  norm_num

private theorem cubic_autocorr_log_two_le :
    autocorr cubicWindow (Real.log 2) ≤ -(33 / 100 : ℝ) * (2 / 105) := by
  have hl : (693147 / 1000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hu : Real.log 2 ≤ 693148 / 1000000 := by linarith only [Real.log_two_lt_d9]
  have hp : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [show autocorr cubicWindow (Real.log 2) = cubicCorrPoly (Real.log 2) from
    cubicWindow_autocorr hp (by linarith only [hu])]
  have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147 / 1000000) hl 2
  have h3 := pow_le_pow_left₀ hp hu 3
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 693147 / 1000000) hl 5
  have h7 := pow_le_pow_left₀ hp hu 7
  norm_num at h2 h3 h5 h7
  unfold cubicCorrPoly
  linarith only [h2, h3, h5, h7]

private theorem primeJumpWeight_two_ge : (49 / 100 : ℝ) ≤ primeJumpWeight 2 := by
  have hs : Real.sqrt 2 ≤ 14143 / 10000 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  unfold primeJumpWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
  linarith only [hs, Real.log_two_gt_d9]

private theorem cosh_quarter_sq_le : Real.cosh (1 / 4 : ℝ) ^ 2 ≤ 16 / 15 := by
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


private theorem cubicWindow_polar_cost_le :
    sinhPairing cubicWindow ^ 2 / 2 ≤ (7 / 225 : ℝ) * (2 / 105) := by
  have hI : Integrable (fun x : ℝ => Real.cosh (1 / 4 : ℝ) * (x * cubicWindow x)) :=
    ((continuous_const.mul (continuous_id.mul continuous_cubicWindow)).integrable_of_hasCompactSupport
      compact_cubicWindow.mul_left.mul_left)
  have hb : ∀ x : ℝ, ‖cubicWindow x * (2 * Real.sinh (x / 2))‖ ≤
      Real.cosh (1 / 4 : ℝ) * (x * cubicWindow x) := by
    intro x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · have hxa : |x| ≤ 1 / 2 := abs_le.mpr hx
      have hcosh : Real.cosh (|x| / 2) ≤ Real.cosh (1 / 4 : ℝ) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : 0 ≤ |x| / 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        linarith only [hxa]
      have hs : |Real.sinh (x / 2)| ≤ |x| / 2 * Real.cosh (1 / 4 : ℝ) := by
        rw [Real.abs_sinh, abs_div, abs_two]
        exact (ArithmeticIncidencePositivity.sinh_le_mul_cosh (by positivity)).trans
          (mul_le_mul_of_nonneg_left hcosh (by positivity))
      have hxf : |cubicWindow x| * |x| = x * cubicWindow x := by
        simp only [cubicWindow, abs_mul, abs_of_nonneg (le_max_right (1 - 4 * x ^ 2) 0)]
        rw [mul_right_comm, ← sq, sq_abs]
        ring
      calc ‖cubicWindow x * (2 * Real.sinh (x / 2))‖
          = (2 * |cubicWindow x|) * |Real.sinh (x / 2)| := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
              ring
        _ ≤ (2 * |cubicWindow x|) * (|x| / 2 * Real.cosh (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = Real.cosh (1 / 4 : ℝ) * (|cubicWindow x| * |x|) := by ring
        _ = Real.cosh (1 / 4 : ℝ) * (x * cubicWindow x) := by rw [hxf]
    · rw [cubicWindow_outside hx]
      simp
  have hN := norm_integral_le_of_norm_le hI (Eventually.of_forall hb)
  rw [integral_const_mul, cubicWindow_position_moment, Real.norm_eq_abs] at hN
  change |sinhPairing cubicWindow| ≤ Real.cosh (1 / 4 : ℝ) * (1 / 30) at hN
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hN 2
  rw [sq_abs, mul_pow] at hsq
  norm_num at hsq
  nlinarith only [hsq, cosh_quarter_sq_le]

/-- The first prime contribution repairs the cubic's negative frozen direction. -/
theorem cubicWindow_complete_first_stage_pos :
    (1 / 100 : ℝ) * (∫ x, cubicWindow x ^ 2) <
      EF.gammaBracket 0 * (∫ x, cubicWindow x ^ 2) + biScaleLevyEnergy cubicWindow -
        2 * primeJumpWeight 2 * autocorr cubicWindow (Real.log 2) -
        sinhPairing cubicWindow ^ 2 / 2 := by
  rw [cubicWindow_mass, cubic_gamma_jump_split]
  have hg := gamma_origin_bounds.1
  have ht := gamma_tail_one_bounds.1
  have hj := cubicJump_inner_ge
  have hp := cubicWindow_polar_cost_le
  have hc := cubic_autocorr_log_two_le
  have hw := primeJumpWeight_two_ge
  have hprime : 2 * primeJumpWeight 2 * autocorr cubicWindow (Real.log 2) ≤
      -(1617 / 5000 : ℝ) * (2 / 105) := by
    have hc0 : autocorr cubicWindow (Real.log 2) ≤ 0 := by linarith only [hc]
    have h1 := mul_le_mul_of_nonpos_right hw hc0
    have h2 := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 49 / 100)
    linarith only [h1, h2]
  linarith only [hg, ht, hj, hp, hprime, Real.log_two_gt_d9, Real.pi_gt_d4]


private def cubicSource : C_c(ℝ, ℝ) :=
  ⟨⟨cubicWindow, continuous_cubicWindow⟩, compact_cubicWindow⟩

private theorem cubicSource_jump_integrable :
    IntegrableOn (fun t => (autocorr cubicSource 0 - autocorr cubicSource t) *
      archLevySinhWeight t) (Ioi (0 : ℝ)) := by
  change IntegrableOn (fun t => (autocorr cubicWindow 0 - autocorr cubicWindow t) *
    archLevySinhWeight t) (Ioi (0 : ℝ))
  rw [cubic_autocorr_zero]
  exact integrable_cubicJump

private theorem cubic_prime_sum :
    (∑' n : ℕ, primeTerm (autocorr cubicWindow) n) =
      primeJumpWeight 2 * autocorr cubicWindow (Real.log 2) := by
  rw [tsum_eq_single 2 (fun n hn => ?_)]
  · unfold primeTerm SignedPrimePolar.primeWeight primeJumpWeight
    rw [if_pos (by norm_num : 2 ≤ (2 : ℕ))]
    norm_num only [Nat.cast_ofNat]
  · by_cases h2 : 2 ≤ n
    · have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hlog : 1 < Real.log n :=
        lt_of_lt_of_le (by linarith only [Real.log_three_gt_d9])
          (Real.log_le_log (by norm_num) h3)
      have hz : autocorr cubicWindow (Real.log n) = 0 := cubicWindow_autocorr_tail hlog
      simp only [primeTerm, if_pos h2, hz, mul_zero]
    · simp only [primeTerm, if_neg h2]

private theorem cubic_polar_identity :
    2 * (∫ t in Ici (0 : ℝ), polarDensity t * autocorr cubicWindow t) =
      -(sinhPairing cubicWindow ^ 2 / 2) := by
  have hm := integral_polar_autocorr_eq_moments cubicSource
  have hp := pole_eq_pairings cubicWindow continuous_cubicWindow compact_cubicWindow
  have hc := coshPairing_eq_zero_of_odd cubicWindow_odd
  have he1 : (∫ u, Real.exp (u / 2) * cubicSource u) =
      ∫ u, cubicWindow u * Real.exp (u / 2) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun u => mul_comm _ _
  have he2 : (∫ u, Real.exp (-(u / 2)) * cubicSource u) =
      ∫ u, cubicWindow u * Real.exp (-u / 2) := by
    apply integral_congr_ae
    filter_upwards with u
    change Real.exp (-(u / 2)) * cubicWindow u = cubicWindow u * Real.exp (-u / 2)
    rw [neg_div]
    ring
  rw [he1, he2] at hm
  change (∫ t in Ici (0 : ℝ), polarDensity t * autocorr cubicWindow t) = _ at hm
  rw [hm]
  rw [hc] at hp
  linarith only [hp]

/-- The complete form on the cubic contains exactly the prime `2` fold. -/
theorem cubicWindow_weilQuad_eq :
    weilQuad cubicWindow = EF.gammaBracket 0 * (2 / 105) + biScaleLevyEnergy cubicWindow -
      2 * primeJumpWeight 2 * autocorr cubicWindow (Real.log 2) -
      sinhPairing cubicWindow ^ 2 / 2 := by
  have h := re_weilFullFunctional_eq_of_compact_finite_jump cubicSource cubicSource_jump_integrable
  change weilQuad cubicWindow = EF.gammaBracket 0 * autocorr cubicWindow 0 +
    biScaleLevyEnergy cubicWindow - 2 * fullPairing (autocorr cubicWindow) at h
  rw [fullPairing, cubic_prime_sum, cubic_autocorr_zero] at h
  linarith only [h, cubic_polar_identity]

/-- Prime `2` gives strict positivity on the same cubic whose frozen form is negative. -/
theorem cubicWindow_weilQuad_pos :
    (1 / 100 : ℝ) * (∫ x, cubicWindow x ^ 2) < weilQuad cubicWindow := by
  rw [cubicWindow_weilQuad_eq]
  simpa only [cubicWindow_mass] using cubicWindow_complete_first_stage_pos

private theorem cubicWindow_frozen_value_neg :
    weilQuad cubicWindow + 2 * primeJumpWeight 2 * autocorr cubicWindow (Real.log 2) <
      -(29 / 2100 : ℝ) * (∫ x, cubicWindow x ^ 2) := by
  rw [cubicWindow_weilQuad_eq]
  have h := cubicWindow_frozen_archimedean_neg
  rw [cubicWindow_mass] at h ⊢
  linarith only [h, sq_nonneg (sinhPairing cubicWindow)]


private theorem cubic_enlarged_window_level :
    CohomologyOfWindowsOfSpecZ.windowLevel (21 / 20) = 2 := by
  unfold CohomologyOfWindowsOfSpecZ.windowLevel
  apply (Nat.floor_eq_iff (Real.exp_pos (21 / 20 : ℝ)).le).mpr
  constructor
  · have h : Real.log 2 ≤ (21 / 20 : ℝ) := by linarith only [Real.log_two_lt_d9]
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Nat.cast_ofNat] using
      Real.exp_le_exp.mpr h
  · have h : (21 / 20 : ℝ) < Real.log 3 := by linarith only [Real.log_three_gt_d9]
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3), Nat.cast_ofNat,
      show (2 : ℝ) + 1 = 3 by norm_num] using Real.exp_lt_exp.mpr h

/-- A smooth first-stage test has negative frozen energy and positive complete energy. -/
theorem exists_first_stage_negative_frozen_positive_complete :
    ∃ H : ℝ → ℝ, CohomologyOfWindowsOfSpecZ.IsWindowTest (21 / 20) H ∧
      stageForm 1 H < 0 ∧ 0 < weilQuad H := by
  have hf2 : MemLp cubicWindow 2 volume :=
    continuous_cubicWindow.memLp_of_hasCompactSupport compact_cubicWindow
  have hfR : ∀ x : ℝ, 1 / 2 < |x| → cubicWindow x = 0 := fun x hx =>
    cubicWindow_outside (fun h => (not_le.mpr hx) (abs_le.mpr h))
  obtain ⟨M, hMnorm⟩ := continuous_cubicWindow.bounded_above_of_compact_support compact_cubicWindow
  have hM : ∀ x, |cubicWindow x| ≤ M := fun x => by
    simpa only [Real.norm_eq_abs] using hMnorm x
  have hfull : Tendsto (fun k : ℕ => weilQuad (CHMDDoobGraph.smooth cubicWindow k)) atTop
      (𝓝 (weilQuad cubicWindow)) :=
    re_weilFullFunctional_smooth_tendsto cubicSource cubicSource_jump_integrable
  have hcorr := autocorr_smooth_tendsto continuous_cubicWindow hM hfR (Real.log 2)
  have hfrozen := hfull.add (hcorr.const_mul (2 * primeJumpWeight 2))
  have hpos : 0 < weilQuad cubicWindow := by
    have h := cubicWindow_weilQuad_pos
    rw [cubicWindow_mass] at h
    linarith only [h]
  have hneg : weilQuad cubicWindow + 2 * primeJumpWeight 2 * autocorr cubicWindow (Real.log 2) < 0 := by
    have h := cubicWindow_frozen_value_neg
    rw [cubicWindow_mass] at h
    linarith only [h]
  have evpos := hfull.eventually (Ioi_mem_nhds hpos)
  have evneg := hfrozen.eventually (Iio_mem_nhds hneg)
  obtain ⟨k, hk, hkpos, hkneg⟩ := ((eventually_ge_atTop 10).and (evpos.and evneg)).exists
  have hkr : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hrad : 1 / (4 * ((k : ℝ) + 1)) ≤ (1 / 40 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [hkr])
  have hsupp : ∀ x : ℝ, 21 / 40 < |x| → CHMDDoobGraph.smooth cubicWindow k x = 0 := by
    intro x hx
    change (∫ t, CHMDDoobGraph.mollifier k t * cubicWindow (x - t)) = 0
    apply integral_eq_zero_of_ae
    filter_upwards with t
    change CHMDDoobGraph.mollifier k t * cubicWindow (x - t) = 0
    by_cases ht : 1 / (4 * ((k : ℝ) + 1)) ≤ |t|
    · have hm : CHMDDoobGraph.mollifier k t = 0 := by
        apply Function.notMem_support.mp
        change t ∉ Function.support ((_root_.RHTower.WeilOneSided.narrowBump k).normed volume)
        rw [(_root_.RHTower.WeilOneSided.narrowBump k).support_normed_eq, Metric.mem_ball,
          dist_zero_right, Real.norm_eq_abs]
        exact not_lt.mpr ht
      rw [hm, zero_mul]
    · rw [hfR _ (by linarith only [abs_sub_abs_le_abs_sub x t, not_le.mp ht, hx, hrad]), mul_zero]
  let H : ℝ → ℝ := fun x => CHMDDoobGraph.smooth cubicWindow k (x + 21 / 40)
  have hH : CohomologyOfWindowsOfSpecZ.IsWindowTest (21 / 20) H := by
    refine ⟨(CHMDDoobGraph.smooth_contDiff hf2 k).comp (contDiff_id.add contDiff_const), ?_⟩
    intro x hx
    apply hsupp
    by_contra hn
    have ha := abs_le.mp (not_lt.mp hn)
    exact hx ⟨by linarith only [ha.1], by linarith only [ha.2]⟩
  have hQ : weilQuad H = weilQuad (CHMDDoobGraph.smooth cubicWindow k) := by
    simpa only [H, sub_neg_eq_add] using
      weilQuad_comp_sub (CHMDDoobGraph.smooth cubicWindow k) (-(21 / 40 : ℝ))
  have hC : autocorr H (Real.log 2) =
      autocorr (CHMDDoobGraph.smooth cubicWindow k) (Real.log 2) := by
    change (∫ x, CHMDDoobGraph.smooth cubicWindow k (x + 21 / 40) *
      CHMDDoobGraph.smooth cubicWindow k (x + Real.log 2 + 21 / 40)) =
      ∫ x, CHMDDoobGraph.smooth cubicWindow k x * CHMDDoobGraph.smooth cubicWindow k (x + Real.log 2)
    calc _ = ∫ x, CHMDDoobGraph.smooth cubicWindow k (x + 21 / 40) *
        CHMDDoobGraph.smooth cubicWindow k ((x + 21 / 40) + Real.log 2) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [show x + Real.log 2 + 21 / 40 = (x + 21 / 40) + Real.log 2 by ring]
      _ = _ := integral_add_right_eq_self
        (fun x : ℝ => CHMDDoobGraph.smooth cubicWindow k x *
          CHMDDoobGraph.smooth cubicWindow k (x + Real.log 2)) (21 / 40 : ℝ)
  have hlocal := CohomologyOfWindowsOfSpecZ.weilQuad_eq_markovForm_windowLevel hH
  rw [cubic_enlarged_window_level] at hlocal
  have hstep := markovForm_succ hH.continuous hH.hasCompactSupport (N := 1) (by norm_num)
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hstep
  have hstage : stageForm 1 H = weilQuad H + 2 * primeJumpWeight 2 * autocorr H (Real.log 2) := by
    unfold stageForm
    change markovForm 2 H = markovForm 1 H - 2 * primeJumpWeight 2 * autocorr H (Real.log 2) at hstep
    linarith only [hstep, hlocal]
  refine ⟨H, hH, ?_, ?_⟩
  · rw [hstage, hQ, hC]
    exact hkneg
  · rw [hQ]
    exact hkpos

/-- The exit-charge loan fails on a positive complete test already at the first stage. -/
theorem exists_first_stage_positive_exit_loan_failure :
    ∃ H : ℝ → ℝ, CohomologyOfWindowsOfSpecZ.IsWindowTest (21 / 20) H ∧
      0 < weilQuad H ∧ stageForm 1 H <
        archLevyAntideriv (21 / 20 - Real.log 2) *
          ∫ x, collarWeight (21 / 20) (21 / 20 - Real.log 2) x * H x ^ 2 := by
  obtain ⟨H, hH, hneg, hpos⟩ := exists_first_stage_negative_frozen_positive_complete
  have he : 0 < (21 / 20 : ℝ) - Real.log 2 := by linarith only [Real.log_two_lt_d9]
  have hm : 0 ≤ ∫ x, collarWeight (21 / 20) (21 / 20 - Real.log 2) x * H x ^ 2 :=
    integral_nonneg fun x => mul_nonneg (collarWeight_nonneg _ _ _) (sq_nonneg _)
  have hΩ := (archLevyAntideriv_pos he).le
  exact ⟨H, hH, hpos, lt_of_lt_of_le hneg (mul_nonneg hΩ hm)⟩

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.cubicWindow_frozen_archimedean_neg
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.cubicWindow_weilQuad_pos
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.exists_first_stage_negative_frozen_positive_complete
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.exists_first_stage_positive_exit_loan_failure
