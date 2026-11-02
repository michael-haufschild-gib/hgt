import GaloisForLFunctions.WindowTowerOfSpecZ.TheCubicWindowHasExactJumpMoments
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTransferAcrossAStage
import GaloisForLFunctions.ArithmeticIncidencePositivity.SecondOrderSurplusPotential
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit
import GaloisForLFunctions.«arithmetic-positivity-theory».MarkovPoleHyperbolicCapacityAndApertureThresholds

/-!
# A negative frozen direction at the first prime fold

The odd cubic on a unit window tests the distinction between a frozen stage
and the complete form. Its exact correlation retains the sign of the new
prime contribution in comparisons with the Gamma jump kernel.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open scoped CompactlySupported
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole

namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticIncidencePositivity ArithmeticPositivityTheory BiScaleUncertainty

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
  simpa [cubicCorrPoly] using cubicWindow_autocorr (t := 0) le_rfl (by norm_num)

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

end GaloisForLFunctions.WindowTowerOfSpecZ
