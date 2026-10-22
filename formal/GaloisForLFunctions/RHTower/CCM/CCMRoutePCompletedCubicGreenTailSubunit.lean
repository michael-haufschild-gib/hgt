import GaloisForLFunctions.RHTower.FrankensteinCCMRoutePBaseCubicGreenSourceBridge
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspContinuousHalfDensityResidualTail
import GaloisForLFunctions.RHTower.CCM.CCMEndpointFourierJet

/-!
# Strictly subunit completed cubic Green scalar tail

The common CCM/Route-P cubic Green profile has three cofinal scalar channels above the first
prime wall `log 2`: the Route-P prime tail after deleting the atom at `2`, the continuous polar
tail, and the literal archimedean Gamma tail.  This module keeps all three channels at their
source normalization and proves that their signed completed sum has absolute value strictly below
one.

The proof is unconditional.  It uses the existing strict bound on the full primitive Route-P
budget, pays the Gamma tail from the deleted first atom, and bounds the polar tail by an explicit
inverse-cube integral.  This is a scalar cancellation theorem.  It does not assert a trace-norm
bound, construct a relative projection, or identify any operator index with a Xi-zero class.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Literal Gamma-channel integrand of the common cubic Green reporter. -/
def ccmRoutePBaseCubicGreenGammaIntegrand (h : ℝ) : ℝ :=
  ccmRoutePBaseCubicGreenLogProfile h * ccmPublishedArchimedeanDensity h

/-- Continuous polar-channel integrand of the common cubic Green reporter. -/
def ccmRoutePBaseCubicGreenPolarIntegrand (h : ℝ) : ℝ :=
  ccmRoutePBaseCubicGreenLogProfile h * (2 * Real.cosh (h / 2))

/-- Explicit positive-half-line form of the Gamma-channel integrand. -/
def ccmRoutePBaseCubicGreenGammaExplicit (h : ℝ) : ℝ :=
  Real.exp (-h) / (4 * h ^ (3 : ℕ) * (1 - Real.exp (-2 * h)))

/-- Explicit positive-half-line form of the polar-channel integrand. -/
def ccmRoutePBaseCubicGreenPolarExplicit (h : ℝ) : ℝ :=
  (1 + Real.exp (-h)) / (4 * h ^ (3 : ℕ))

theorem ccmRoutePBaseCubicGreenGammaIntegrand_eq_explicit
    {h : ℝ} (hh : Real.log 2 < h) :
    ccmRoutePBaseCubicGreenGammaIntegrand h =
      ccmRoutePBaseCubicGreenGammaExplicit h := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 : 0 < h := hlog.trans hh
  have hden : 1 - Real.exp (-2 * h) ≠ 0 := by
    have : Real.exp (-2 * h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hexp : Real.exp (-h / 2) * Real.exp (-h / 2) = Real.exp (-h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ccmRoutePBaseCubicGreenGammaIntegrand,
    ccmRoutePBaseCubicGreenLogProfile, max_eq_left hh.le,
    ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hh0,
    ccmRoutePBaseCubicGreenGammaExplicit]
  calc
    Real.exp (-h / 2) / (4 * h ^ (3 : ℕ)) *
          (Real.exp (-h / 2) / (1 - Real.exp (-2 * h))) =
        (Real.exp (-h / 2) * Real.exp (-h / 2)) /
          (4 * h ^ (3 : ℕ) * (1 - Real.exp (-2 * h))) := by
      field_simp [hh0.ne', hden]
    _ = Real.exp (-h) / (4 * h ^ (3 : ℕ) * (1 - Real.exp (-2 * h))) := by
      rw [hexp]

theorem ccmRoutePBaseCubicGreenPolarIntegrand_eq_explicit
    {h : ℝ} (hh : Real.log 2 < h) :
    ccmRoutePBaseCubicGreenPolarIntegrand h =
      ccmRoutePBaseCubicGreenPolarExplicit h := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 : 0 < h := hlog.trans hh
  have hnum : Real.exp (-h / 2) * (2 * Real.cosh (h / 2)) =
      1 + Real.exp (-h) := by
    rw [Real.cosh_eq]
    calc
      Real.exp (-h / 2) *
          (2 * ((Real.exp (h / 2) + Real.exp (-(h / 2))) / 2)) =
        Real.exp (-h / 2) * Real.exp (h / 2) +
          Real.exp (-h / 2) * Real.exp (-h / 2) := by ring
      _ = Real.exp (-h / 2 + h / 2) +
          Real.exp (-h / 2 + -h / 2) := by
        rw [Real.exp_add, Real.exp_add]
      _ = 1 + Real.exp (-h) := by
        rw [show -h / 2 + h / 2 = 0 by ring,
          show -h / 2 + -h / 2 = -h by ring, Real.exp_zero]
  rw [ccmRoutePBaseCubicGreenPolarIntegrand,
    ccmRoutePBaseCubicGreenLogProfile, max_eq_left hh.le,
    ccmRoutePBaseCubicGreenPolarExplicit]
  calc
    Real.exp (-h / 2) / (4 * h ^ (3 : ℕ)) * (2 * Real.cosh (h / 2)) =
        (Real.exp (-h / 2) * (2 * Real.cosh (h / 2))) /
          (4 * h ^ (3 : ℕ)) := by ring
    _ = (1 + Real.exp (-h)) / (4 * h ^ (3 : ℕ)) := by rw [hnum]

theorem ccmRoutePBaseCubicGreenGammaExplicit_nonneg
    {h : ℝ} (hh : Real.log 2 < h) :
    0 ≤ ccmRoutePBaseCubicGreenGammaExplicit h := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 : 0 < h := hlog.trans hh
  have he : Real.exp (-2 * h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_nonneg (Real.exp_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hh0.le 3))
      (sub_nonneg.mpr he.le))

private theorem exp_neg_le_half_of_log_two_le
    {h : ℝ} (hh : Real.log 2 ≤ h) :
    Real.exp (-h) ≤ 1 / 2 := by
  calc
    Real.exp (-h) ≤ Real.exp (-Real.log 2) := by
      rw [Real.exp_le_exp]
      linarith
    _ = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

private theorem exp_neg_two_mul_eq_sq (h : ℝ) :
    Real.exp (-2 * h) = Real.exp (-h) ^ (2 : ℕ) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem ccmRoutePBaseCubicGreenGammaExplicit_le_inv_cube
    {h : ℝ} (hh : Real.log 2 < h) :
    ccmRoutePBaseCubicGreenGammaExplicit h ≤
      (1 / 6 : ℝ) * (h ^ (3 : ℕ))⁻¹ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 : 0 < h := hlog.trans hh
  have he0 : 0 < Real.exp (-h) := Real.exp_pos _
  have hehalf : Real.exp (-h) ≤ 1 / 2 :=
    exp_neg_le_half_of_log_two_le hh.le
  have he2 : Real.exp (-2 * h) = Real.exp (-h) ^ (2 : ℕ) :=
    exp_neg_two_mul_eq_sq h
  have hden : 3 / 4 ≤ 1 - Real.exp (-2 * h) := by
    rw [he2]
    nlinarith [sq_nonneg (Real.exp (-h))]
  have hdenpos : 0 < 1 - Real.exp (-2 * h) :=
    lt_of_lt_of_le (by norm_num) hden
  have hratio : Real.exp (-h) / (1 - Real.exp (-2 * h)) ≤ 2 / 3 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith
  have hfac : 0 ≤ 1 / (4 * h ^ (3 : ℕ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hratio hfac
  rw [ccmRoutePBaseCubicGreenGammaExplicit]
  calc
    Real.exp (-h) / (4 * h ^ (3 : ℕ) * (1 - Real.exp (-2 * h))) =
        (1 / (4 * h ^ (3 : ℕ))) *
          (Real.exp (-h) / (1 - Real.exp (-2 * h))) := by
      field_simp [hh0.ne', hdenpos.ne']
    _ ≤ (1 / (4 * h ^ (3 : ℕ))) * (2 / 3) := hmul
    _ ≤ (1 / 6) * (h ^ (3 : ℕ))⁻¹ := by
      apply le_of_eq
      field_simp [hh0.ne']
      ring_nf

theorem ccmRoutePBaseCubicGreenPolarExplicit_nonneg
    {h : ℝ} (hh : Real.log 2 < h) :
    0 ≤ ccmRoutePBaseCubicGreenPolarExplicit h := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 : 0 < h := hlog.trans hh
  exact div_nonneg (add_nonneg (by norm_num) (Real.exp_nonneg _))
    (mul_nonneg (by norm_num) (pow_nonneg hh0.le 3))

theorem ccmRoutePBaseCubicGreenPolarExplicit_le_inv_cube
    {h : ℝ} (hh : Real.log 2 < h) :
    ccmRoutePBaseCubicGreenPolarExplicit h ≤
      (3 / 8 : ℝ) * (h ^ (3 : ℕ))⁻¹ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 : 0 < h := hlog.trans hh
  have hehalf : Real.exp (-h) ≤ 1 / 2 :=
    exp_neg_le_half_of_log_two_le hh.le
  rw [ccmRoutePBaseCubicGreenPolarExplicit]
  have hden : 0 < 4 * h ^ (3 : ℕ) := by positivity
  have hdiv : (1 + Real.exp (-h)) / (4 * h ^ (3 : ℕ)) ≤
      (3 / 2) / (4 * h ^ (3 : ℕ)) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  calc
    (1 + Real.exp (-h)) / (4 * h ^ (3 : ℕ)) ≤
        (3 / 2) / (4 * h ^ (3 : ℕ)) := hdiv
    _ ≤ (3 / 8) * (h ^ (3 : ℕ))⁻¹ := by
      apply le_of_eq
      field_simp [hh0.ne']
      norm_num

theorem integrableOn_ccmRoutePBaseCubicGreenGammaExplicit :
    IntegrableOn ccmRoutePBaseCubicGreenGammaExplicit (Ioi (Real.log 2)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmajor : IntegrableOn (fun h : ℝ => (1 / 6 : ℝ) * (1 / h ^ (3 : ℕ)))
      (Ioi (Real.log 2)) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_inv_pow
      hlog (k := 3) (by norm_num)).const_mul _
  refine hmajor.mono' (by
    have hn : Measurable (fun h : ℝ => Real.exp (-h)) := by fun_prop
    have hd : Measurable (fun h : ℝ =>
        4 * h ^ (3 : ℕ) * (1 - Real.exp (-2 * h))) := by fun_prop
    exact (hn.div hd).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall fun h hh => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (ccmRoutePBaseCubicGreenGammaExplicit_nonneg hh)]
  simpa only [one_div] using
    ccmRoutePBaseCubicGreenGammaExplicit_le_inv_cube hh

theorem integrableOn_ccmRoutePBaseCubicGreenPolarExplicit :
    IntegrableOn ccmRoutePBaseCubicGreenPolarExplicit (Ioi (Real.log 2)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmajor : IntegrableOn (fun h : ℝ => (3 / 8 : ℝ) * (1 / h ^ (3 : ℕ)))
      (Ioi (Real.log 2)) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_inv_pow
      hlog (k := 3) (by norm_num)).const_mul _
  refine hmajor.mono' (by
    have hn : Measurable (fun h : ℝ => 1 + Real.exp (-h)) := by fun_prop
    have hd : Measurable (fun h : ℝ => 4 * h ^ (3 : ℕ)) := by fun_prop
    exact (hn.div hd).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall fun h hh => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (ccmRoutePBaseCubicGreenPolarExplicit_nonneg hh)]
  simpa only [one_div] using
    ccmRoutePBaseCubicGreenPolarExplicit_le_inv_cube hh

/-- Infinite Gamma tail above the first-prime wall. -/
def ccmRoutePBaseCubicGreenGammaTail : ℝ :=
  ∫ h in Ioi (Real.log 2), ccmRoutePBaseCubicGreenGammaIntegrand h

/-- Infinite polar tail above the first-prime wall. -/
def ccmRoutePBaseCubicGreenPolarTail : ℝ :=
  ∫ h in Ioi (Real.log 2), ccmRoutePBaseCubicGreenPolarIntegrand h

theorem ccmRoutePBaseCubicGreenGammaTail_eq_explicit :
    ccmRoutePBaseCubicGreenGammaTail =
      ∫ h in Ioi (Real.log 2), ccmRoutePBaseCubicGreenGammaExplicit h := by
  rw [ccmRoutePBaseCubicGreenGammaTail]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
  exact ccmRoutePBaseCubicGreenGammaIntegrand_eq_explicit hh

theorem ccmRoutePBaseCubicGreenPolarTail_eq_explicit :
    ccmRoutePBaseCubicGreenPolarTail =
      ∫ h in Ioi (Real.log 2), ccmRoutePBaseCubicGreenPolarExplicit h := by
  rw [ccmRoutePBaseCubicGreenPolarTail]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
  exact ccmRoutePBaseCubicGreenPolarIntegrand_eq_explicit hh

theorem ccmRoutePBaseCubicGreenGammaTail_nonneg :
    0 ≤ ccmRoutePBaseCubicGreenGammaTail := by
  rw [ccmRoutePBaseCubicGreenGammaTail_eq_explicit]
  apply MeasureTheory.integral_nonneg_of_ae
  refine (ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall fun h hh =>
      ccmRoutePBaseCubicGreenGammaExplicit_nonneg hh)

theorem ccmRoutePBaseCubicGreenPolarTail_nonneg :
    0 ≤ ccmRoutePBaseCubicGreenPolarTail := by
  rw [ccmRoutePBaseCubicGreenPolarTail_eq_explicit]
  apply MeasureTheory.integral_nonneg_of_ae
  refine (ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall fun h hh =>
      ccmRoutePBaseCubicGreenPolarExplicit_nonneg hh)

theorem ccmRoutePBaseCubicGreenGammaTail_lt_three_sixteenths :
    ccmRoutePBaseCubicGreenGammaTail < 3 / 16 := by
  rw [ccmRoutePBaseCubicGreenGammaTail_eq_explicit]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmajor : IntegrableOn (fun h : ℝ => (1 / 6 : ℝ) * (1 / h ^ (3 : ℕ)))
      (Ioi (Real.log 2)) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_inv_pow
      hlog (k := 3) (by norm_num)).const_mul _
  have hle :
      (∫ h in Ioi (Real.log 2), ccmRoutePBaseCubicGreenGammaExplicit h) ≤
        ∫ h in Ioi (Real.log 2), (1 / 6 : ℝ) * (1 / h ^ (3 : ℕ)) := by
    apply integral_mono_ae integrableOn_ccmRoutePBaseCubicGreenGammaExplicit hmajor
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun h hh => ?_)
    simpa only [one_div] using
      ccmRoutePBaseCubicGreenGammaExplicit_le_inv_cube hh
  rw [integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_inv_cube hlog] at hle
  have hLsq : (4 / 9 : ℝ) < (Real.log 2) ^ (2 : ℕ) := by
    nlinarith [two_thirds_lt_log_two]
  have hinv : ((Real.log 2) ^ (2 : ℕ))⁻¹ < ((4 / 9 : ℝ))⁻¹ := by
    exact (inv_lt_inv₀ (sq_pos_of_pos hlog) (by norm_num)).2 hLsq
  norm_num at hinv hle
  nlinarith

theorem ccmRoutePBaseCubicGreenPolarTail_lt_one :
    ccmRoutePBaseCubicGreenPolarTail < 1 := by
  rw [ccmRoutePBaseCubicGreenPolarTail_eq_explicit]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmajor : IntegrableOn (fun h : ℝ => (3 / 8 : ℝ) * (1 / h ^ (3 : ℕ)))
      (Ioi (Real.log 2)) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_inv_pow
      hlog (k := 3) (by norm_num)).const_mul _
  have hle :
      (∫ h in Ioi (Real.log 2), ccmRoutePBaseCubicGreenPolarExplicit h) ≤
        ∫ h in Ioi (Real.log 2), (3 / 8 : ℝ) * (1 / h ^ (3 : ℕ)) := by
    apply integral_mono_ae integrableOn_ccmRoutePBaseCubicGreenPolarExplicit hmajor
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun h hh => ?_)
    simpa only [one_div] using
      ccmRoutePBaseCubicGreenPolarExplicit_le_inv_cube hh
  rw [integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_inv_cube hlog] at hle
  have hLsq : (4 / 9 : ℝ) < (Real.log 2) ^ (2 : ℕ) := by
    nlinarith [two_thirds_lt_log_two]
  have hinv : ((Real.log 2) ^ (2 : ℕ))⁻¹ < ((4 / 9 : ℝ))⁻¹ := by
    exact (inv_lt_inv₀ (sq_pos_of_pos hlog) (by norm_num)).2 hLsq
  norm_num at hinv hle
  nlinarith

theorem routePPrimeGammaBaseCubicWeight_nonneg (n : ℕ) :
    0 ≤ routePPrimeGammaBaseCubicWeight n := by
  rw [routePPrimeGammaBaseCubicWeight]
  exact mul_nonneg (by norm_num) (routePPrimeGammaCubicWeight_nonneg n)

theorem routePPrimeGammaBaseCubicWeight_two_eq :
    routePPrimeGammaBaseCubicWeight 2 =
      1 / (8 * (Real.log 2) ^ (2 : ℕ)) := by
  rw [routePPrimeGammaBaseCubicWeight, routePPrimeGammaCubicWeight,
    vonMangoldtInverseLogPowerWeight, finiteVonMangoldtRealWeight,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  norm_num
  field_simp [hlog]
  ring

theorem three_sixteenths_lt_routePPrimeGammaBaseCubicWeight_two :
    (3 / 16 : ℝ) < routePPrimeGammaBaseCubicWeight 2 := by
  rw [routePPrimeGammaBaseCubicWeight_two_eq]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : (Real.log 2) ^ (2 : ℕ) < 2 / 3 := by
    nlinarith [Real.log_two_lt_d9]
  rw [lt_div_iff₀ (by positivity : 0 < 8 * (Real.log 2) ^ (2 : ℕ))]
  nlinarith

/-- Arithmetic prime tail after deleting the atom at the first-prime wall. -/
def ccmRoutePBaseCubicGreenOpenPrimeTail : ℝ :=
  routePPrimitiveBaseCauchyCubicTraceBudget -
    routePPrimeGammaBaseCubicWeight 2

theorem ccmRoutePBaseCubicGreenOpenPrimeTail_nonneg :
    0 ≤ ccmRoutePBaseCubicGreenOpenPrimeTail := by
  have hterm := summable_routePPrimeGammaBaseCubicWeight.le_tsum 2
    (fun n _ => routePPrimeGammaBaseCubicWeight_nonneg n)
  rw [tsum_routePPrimeGammaBaseCubicWeight_eq_budget] at hterm
  exact sub_nonneg.mpr hterm

/-- Cofinal signed scalar source after prime, polar, and Gamma completion. -/
def ccmRoutePCompletedCubicGreenTail : ℝ :=
  ccmRoutePBaseCubicGreenOpenPrimeTail -
    ccmRoutePBaseCubicGreenPolarTail +
      ccmRoutePBaseCubicGreenGammaTail

/-- **Completed scalar survivor.**  The full signed cofinal cubic Green tail is strictly subunit. -/
theorem abs_ccmRoutePCompletedCubicGreenTail_lt_one :
    |ccmRoutePCompletedCubicGreenTail| < 1 := by
  have hbudget := routePPrimitiveBaseCauchyCubicTraceBudget_lt_one
  have hgamma := ccmRoutePBaseCubicGreenGammaTail_lt_three_sixteenths
  have hgamma0 := ccmRoutePBaseCubicGreenGammaTail_nonneg
  have hatom := three_sixteenths_lt_routePPrimeGammaBaseCubicWeight_two
  have hopen := ccmRoutePBaseCubicGreenOpenPrimeTail_nonneg
  have hpolar0 := ccmRoutePBaseCubicGreenPolarTail_nonneg
  have hpolar := ccmRoutePBaseCubicGreenPolarTail_lt_one
  rw [abs_lt]
  constructor
  · rw [ccmRoutePCompletedCubicGreenTail]
    linarith
  · rw [ccmRoutePCompletedCubicGreenTail,
      ccmRoutePBaseCubicGreenOpenPrimeTail]
    linarith

end

end RHTower
