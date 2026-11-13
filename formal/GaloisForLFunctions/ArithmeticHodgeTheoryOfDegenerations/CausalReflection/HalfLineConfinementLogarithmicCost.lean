import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ActualHalfLineLevyEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineConfinementCorrelation
import GaloisForLFunctions.BiScaleUncertainty.KreinKantorovichMeasureTransportAndPrimePolarPairing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmic cost of half-line concentration

Small exponential excess forces a correlation deficit beyond its own scale.
Integrating against the singular Lévy kernel gives a coefficient-one
logarithmic lower bound throughout the actual Gamma domain.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri BiScaleUncertainty

private theorem sqrt_mul_rpow_neg_half {r : ℝ} (hr : 0 < r) :
    Real.sqrt r * r ^ (-(1 / 2 : ℝ)) = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hr]
  norm_num

private theorem integral_sqrt_rpow_tail {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (∫ x in r..1, Real.sqrt r * x ^ (-(3 / 2 : ℝ))) = 2 * (1 - Real.sqrt r) := by
  have hzero : (0 : ℝ) ∉ uIcc r 1 := by
    rw [uIcc_of_le hr1]
    intro h
    exact (not_le_of_gt hr) h.1
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by norm_num, hzero⟩),
    show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by ring, Real.one_rpow]
  have hmul := sqrt_mul_rpow_neg_half hr
  norm_num
  nlinarith only [hmul]

private theorem integral_reciprocal_on_positive {r : ℝ} (hr : 0 < r) :
    (∫ x in r..1, 1 / x) = -Real.log r := by
  simp_rw [one_div]
  rw [integral_inv_of_pos hr zero_lt_one, one_div, Real.log_inv]

private theorem sqrt_div_div {r x : ℝ} (hr : 0 ≤ r) (hx : 0 < x) :
    Real.sqrt (r / x) / x = Real.sqrt r * x ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_div hr, Real.rpow_neg hx.le,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  field_simp

private theorem levy_weight_lower {x : ℝ} (hx : 0 < x) :
    1 / x - 1 / 2 ≤ archLevySinhWeight x := by
  have h := div_le_div_of_nonneg_right (Real.add_one_le_exp (-x / 2)) hx.le
  have he : (-x / 2 + 1) / x = 1 / x - 1 / 2 := by field_simp; ring
  rw [he] at h
  exact h.trans (archLevySinhWeight_ge_exp_neg_half_div hx le_rfl)

private theorem correlation_cost_lower {c r x : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hrx : r ≤ x) (hc : c ≤ Real.sqrt (r / x)) :
    1 / x - Real.sqrt r * x ^ (-(3 / 2 : ℝ)) - 1 / 2 ≤
      (1 - c) * archLevySinhWeight x := by
  have hs : Real.sqrt (r / x) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_iff₀ hx).mpr (by simpa only [one_mul] using hrx))
  calc
    _ = (1 - Real.sqrt (r / x)) * (1 / x - 1 / 2) - Real.sqrt (r / x) / 2 := by
      rw [← sqrt_div_div hr.le hx]
      ring
    _ ≤ (1 - Real.sqrt (r / x)) * (1 / x - 1 / 2) :=
      sub_le_self _ (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
    _ ≤ (1 - Real.sqrt (r / x)) * archLevySinhWeight x :=
      mul_le_mul_of_nonneg_left (levy_weight_lower hx) (sub_nonneg.mpr hs)
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_left hc 1) (archLevySinhWeight_pos hx).le

/-- Unit mass confined near the boundary pays a logarithmic Lévy energy cost. -/
theorem CriticalHalfLineEnergyDomain.biScaleLevyEnergy_log_defect_lower {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hm : (∫ u, F u ^ 2) = 1) :
    -Real.log (criticalHalfLineExponentialDefect F) - 5 / 2 ≤ biScaleLevyEnergy F := by
  let d := criticalHalfLineExponentialDefect F
  have hd : 0 < d := hF.exponential_defect_pos (hm.symm ▸ zero_lt_one)
  by_cases hd8 : d < 8
  · let r := d / 8
    have hr : 0 < r := div_pos hd (by norm_num)
    have hr1 : r ≤ 1 := by dsimp only [r]; linarith only [hd8]
    let J : ℝ → ℝ := fun x => (autocorr F 0 - autocorr F x) * archLevySinhWeight x
    have hJ : IntegrableOn J (Ioi 0) := hF.integrableOn_biScaleLevyIntegrand
    have hsub : Ioc r 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hr.trans hx.1
    have hJi : IntervalIntegrable J volume r 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hr1).mpr (hJ.mono_set hsub)
    have hinv : IntervalIntegrable (fun x : ℝ => 1 / x) volume r 1 := by
      apply ContinuousOn.intervalIntegrable_of_Icc hr1
      exact continuousOn_const.div continuousOn_id fun x hx => (hr.trans_le hx.1).ne'
    have hz : (0 : ℝ) ∉ uIcc r 1 := by
      rw [uIcc_of_le hr1]
      intro h
      exact (not_le_of_gt hr) h.1
    have hpow : IntervalIntegrable (fun x : ℝ => Real.sqrt r * x ^ (-(3 / 2 : ℝ))) volume r 1 :=
      (intervalIntegral.intervalIntegrable_rpow (Or.inr hz)).const_mul _
    have hconst : IntervalIntegrable (fun _x : ℝ => (1 / 2 : ℝ)) volume r 1 :=
      continuous_const.intervalIntegrable _ _
    have hmono : (∫ x in r..1, 1 / x - Real.sqrt r * x ^ (-(3 / 2 : ℝ)) - 1 / 2) ≤
        ∫ x in r..1, J x := by
      apply intervalIntegral.integral_mono_on hr1 ((hinv.sub hpow).sub hconst) hJi
      intro x hx
      have hxp : 0 < x := hr.trans_le hx.1
      have hc := hF.abs_correlation_le_sqrt_defect hm hxp
      have he : criticalHalfLineExponentialDefect F / (8 * x) = r / x := by
        dsimp only [r, d]
        ring
      rw [he] at hc
      have hm0 : autocorr F 0 = 1 := by
        rw [AutocorrelationKrein.autocorr_zero_eq, hm]
      change _ ≤ (autocorr F 0 - autocorr F x) * _
      rw [hm0]
      exact correlation_cost_lower hr hxp hx.1 ((le_abs_self _).trans hc)
    have htail : (∫ x in r..1, J x) ≤ biScaleLevyEnergy F := by
      rw [intervalIntegral.integral_of_le hr1]
      apply setIntegral_mono_set hJ
        ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => hF.biScaleLevyIntegrand_nonneg hx)
      exact Eventually.of_forall fun x hx => hsub hx
    have hint : (∫ x in r..1, 1 / x - Real.sqrt r * x ^ (-(3 / 2 : ℝ)) - 1 / 2) =
        -Real.log r - 2 * (1 - Real.sqrt r) - (1 - r) / 2 := by
      rw [intervalIntegral.integral_sub (hinv.sub hpow) hconst,
        intervalIntegral.integral_sub hinv hpow, integral_reciprocal_on_positive hr,
        integral_sqrt_rpow_tail hr hr1, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [hint] at hmono
    have hlog : Real.log r = Real.log d - Real.log 8 := by
      exact Real.log_div hd.ne' (by norm_num)
    rw [hlog] at hmono
    have hlog8 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
    change -Real.log d - 5 / 2 ≤ _
    linarith only [hmono, htail, Real.sqrt_nonneg r, hr, hlog8]
  · have hd1 : 1 ≤ d := by linarith only [le_of_not_gt hd8]
    have hl := Real.log_nonneg hd1
    have hn := hF.biScaleLevyEnergy_nonneg
    change -Real.log d - 5 / 2 ≤ _
    linarith only [hl, hn]

#print axioms CriticalHalfLineEnergyDomain.biScaleLevyEnergy_log_defect_lower

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
