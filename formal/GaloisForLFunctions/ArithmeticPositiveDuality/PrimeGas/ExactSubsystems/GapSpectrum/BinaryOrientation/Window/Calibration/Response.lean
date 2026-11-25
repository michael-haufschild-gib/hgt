import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.VacuumLimit
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference
import GaloisForLFunctions.RHTower.HalfNormalExactScale
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.BlockDeletion

/-! # The invertible vacuum response and its matching slope -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window

open Filter Topology MeasureTheory _root_.RHTower

/-- Continuous derivative of Ein, with value one at the removable origin. -/
def einDerivative (t : ℝ) := GaloisForLFunctions.HTGeometry.expDivOne (-t)

private theorem continuous_einDerivative : Continuous einDerivative := by
  have hc : Continuous (Function.uncurry (fun t u : ℝ => Real.exp (u*(-t)))) :=
    Real.continuous_exp.comp (continuous_snd.mul continuous_fst.neg)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1

theorem einDerivative_pos (t : ℝ) : 0 < einDerivative t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [einDerivative,GaloisForLFunctions.HTGeometry.expDivOne_eq_of_ne (neg_ne_zero.mpr ht.ne)]
    exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr (neg_pos.mpr ht))) (neg_pos.mpr ht)
  · simp [einDerivative,GaloisForLFunctions.HTGeometry.expDivOne_zero]
  · exact GaloisForLFunctions.HTGeometry.expDivOne_pos (neg_nonpos.mpr ht.le)

private theorem einDerivative_agrees {t : ℝ} (ht : t ≠ 0) : einDerivative t = einProfile t := by
  rw [einDerivative,GaloisForLFunctions.HTGeometry.expDivOne_eq_of_ne (neg_ne_zero.mpr ht),
    einProfile,if_neg ht,div_neg,← neg_div,neg_sub]

private theorem ein_regular (v : ℝ) : ein v = ∫ t in (0:ℝ)..v, einDerivative t := by
  unfold ein
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (0:ℝ)] with t ht
  exact fun _ => (einDerivative_agrees ht).symm

theorem ein_derivative (v : ℝ) : HasDerivAt ein (einDerivative v) v := by
  rw [show ein = (fun b => ∫ t in (0:ℝ)..b, einDerivative t) from funext ein_regular]
  exact intervalIntegral.integral_hasDerivAt_right (continuous_einDerivative.intervalIntegrable _ _)
    continuous_einDerivative.aestronglyMeasurable.stronglyMeasurableAtFilter continuous_einDerivative.continuousAt

private theorem scale_integral (a : ℝ) :
    (∫ t in (0:ℝ)..1, (1-Real.exp (-2*a*t))/t) = ein (2*a) := by
  have he : (fun t : ℝ => (1-Real.exp (-2*a*t))/t) = scaledEinProfile (2*a) := by
    funext t
    by_cases ht : t = 0
    · simp [ht,scaledEinProfile]
    · simp only [scaledEinProfile,if_neg ht,neg_mul]
  rw [he,scaledEinProfile_eq,intervalIntegral.integral_const_mul]
  by_cases h : 2*a = 0
  · simp [h,ein]
  · rw [intervalIntegral.integral_comp_mul_left einProfile h,mul_zero,mul_one,smul_eq_mul,ein]
    have ha : a ≠ 0 := fun ha => h (by rw [ha,mul_zero])
    field_simp [ha]

/-- Real vacuum normalization from the unshifted Mertens factor and the finite double-occupation trace. -/
def responseConstant := Real.exp (-Real.eulerMascheroniConstant)*(riemannZeta 2).re

theorem responseConstant_pos : 0 < responseConstant := by
  have h := InverseSpectrum.ShellMixing.gasPartition_pos (⟨2,one_lt_two⟩ : TraceTemperature)
  exact mul_pos (Real.exp_pos _) h

def response (a : ℝ) : ℝ := responseConstant*Real.exp (ein (2*a))

theorem response_pos (a : ℝ) : 0 < response a := mul_pos responseConstant_pos (Real.exp_pos _)

theorem response_derivative (a : ℝ) : HasDerivAt response (2*response a*einDerivative (2*a)) a := by
  have h := ((ein_derivative (2*a)).comp a ((hasDerivAt_id a).const_mul 2)).exp.const_mul responseConstant
  change HasDerivAt response (responseConstant*(Real.exp (ein (2*a))*(einDerivative (2*a)*(2*1)))) a at h
  rwa [show 2*response a*einDerivative (2*a) =
    responseConstant*(Real.exp (ein (2*a))*(einDerivative (2*a)*(2*1))) by unfold response; ring]

theorem response_strictMono : StrictMono response := by
  apply strictMono_of_deriv_pos
  intro a
  rw [(response_derivative a).deriv]
  exact mul_pos (mul_pos zero_lt_two (response_pos a)) (einDerivative_pos _)

theorem continuous_response : Continuous response :=
  continuous_iff_continuousAt.mpr (fun a => (response_derivative a).continuousAt)

/-- The forward finite-window law at every fixed logarithmic drift. -/
theorem reading_fixed (a : ℝ) :
    Tendsto (fun N : ℕ => Real.log N*vacuumProbability N (1/2+a/Real.log N))
      atTop (𝓝 (response a)) := by
  have h := vacuum_critical_window a
  rwa [scale_integral] at h

private theorem negative_ein_le {v : ℝ} (hv : v ≤ 0) : ein v ≤ v := by
  have hb : ∀ t ∈ Set.Icc v 0, (1:ℝ) ≤ einDerivative t := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | hn
    · simp [einDerivative,GaloisForLFunctions.HTGeometry.expDivOne_zero]
    · rw [einDerivative_agrees hn,einProfile,if_neg hn]
      apply (le_div_iff_of_neg (lt_of_le_of_ne ht.2 hn)).mpr
      linarith only [Real.add_one_le_exp (-t)]
  have H := intervalIntegral.integral_mono_on (μ := volume) hv
    (intervalIntegrable_const (c := (1:ℝ))) (continuous_einDerivative.intervalIntegrable _ _) hb
  rw [intervalIntegral.integral_const,smul_eq_mul,mul_one,zero_sub,intervalIntegral.integral_symm (f := einDerivative) 0 v,
    ← ein_regular] at H
  linarith only [H]

theorem response_atBot : Tendsto response atBot (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => 2*a) atBot atBot :=
    tendsto_id.const_mul_atBot zero_lt_two
  have H := (tendsto_const_nhds (x := responseConstant)).mul (Real.tendsto_exp_atBot.comp ht)
  rw [mul_zero] at H
  apply squeeze_zero' (Eventually.of_forall (fun a => (response_pos a).le)) _ H
  filter_upwards [eventually_le_atBot (0:ℝ)] with a ha
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (negative_ein_le (mul_nonpos_of_nonneg_of_nonpos zero_le_two ha))) responseConstant_pos.le

/-- On the positive side the Euler constant cancels, leaving the unrestricted squarefree gas slope. -/
theorem response_slope_atTop :
    Tendsto (fun a : ℝ => response a/(2*a)) atTop (𝓝 (riemannZeta 2).re) := by
  have ht : Tendsto (fun a : ℝ => 2*a) atTop atTop := tendsto_id.const_mul_atTop zero_lt_two
  have H := (tendsto_const_nhds (x := responseConstant)).mul
    ((Real.continuous_exp.tendsto _).comp (tendsto_ein_sub_log.comp ht))
  have hc : responseConstant*Real.exp Real.eulerMascheroniConstant = (riemannZeta 2).re := by
    rw [responseConstant,Real.exp_neg]
    field_simp
  rw [hc] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  dsimp only [Function.comp_apply]
  rw [Real.exp_sub,Real.exp_log (mul_pos zero_lt_two ha),response,mul_div_assoc]

theorem response_atTop : Tendsto response atTop atTop := by
  have hp := InverseSpectrum.ShellMixing.gasPartition_pos (⟨2,one_lt_two⟩ : TraceTemperature)
  have hd : Tendsto (fun a : ℝ => 2*a) atTop atTop := tendsto_id.const_mul_atTop zero_lt_two
  have H := hd.atTop_mul_pos (show 0 < (riemannZeta 2).re from hp) response_slope_atTop
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  change (2*a)*(response a/(2*a)) = response a
  rw [mul_comm,div_mul_cancel₀ _ (mul_ne_zero two_ne_zero ha.ne')]

/-- Every positive limiting reading identifies one drift. -/
def driftCalibration : ℝ ≃o Set.Ioi (0:ℝ) :=
  StrictMono.orderIsoOfSurjective (fun a => ⟨response a,response_pos a⟩) response_strictMono (fun y => by
    obtain ⟨a,ha⟩ := (response_atBot.eventually_lt_const y.property).exists
    obtain ⟨b,hb⟩ := (tendsto_atTop.mp response_atTop y.val).exists
    obtain ⟨c,hc⟩ := intermediate_value_univ a b continuous_response (show y.val ∈ Set.Icc _ _ from ⟨ha.le,hb⟩)
    exact ⟨c,Subtype.ext hc⟩)

theorem driftCalibration_apply (a : ℝ) : (driftCalibration a).val = response a := rfl

#print axioms einDerivative_pos
#print axioms ein_derivative
#print axioms responseConstant_pos
#print axioms response_pos
#print axioms response_derivative
#print axioms response_strictMono
#print axioms continuous_response
#print axioms reading_fixed
#print axioms response_atBot
#print axioms response_slope_atTop
#print axioms response_atTop
#print axioms driftCalibration
#print axioms driftCalibration_apply

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window
