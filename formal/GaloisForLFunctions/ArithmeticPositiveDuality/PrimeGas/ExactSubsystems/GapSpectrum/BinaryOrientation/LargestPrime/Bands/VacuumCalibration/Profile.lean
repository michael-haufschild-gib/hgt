import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Exponent

/-! # The vacuum response of one finite logarithmic prime band -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.VacuumCalibration

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace

def mass (c d a : ℝ) := ∫ v in c..d, Real.exp (-a*v)/v

def response (c d a : ℝ) := Real.exp (-mass c d a)

private theorem integrable_profile {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (a : ℝ) :
    IntervalIntegrable (fun v : ℝ => Real.exp (-a*v)/v) volume c d := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hcd]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div continuousOn_id
    (fun v hv => (hc.trans_le hv.1).ne')

theorem response_zero {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) : response c d 0 = c/d := by
  simp only [response,mass,neg_zero,zero_mul,Real.exp_zero,integral_one_div_of_pos hc (hc.trans_le hcd),
    Real.exp_neg,Real.exp_log (div_pos (hc.trans_le hcd) hc),inv_div]

/-- Above the pole the surviving jump intensity decays exponentially in the positive drift. -/
theorem mass_atTop {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (mass c d) atTop (𝓝 0) := by
  have he : Tendsto (fun a : ℝ => Real.exp (-a*c)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hc))
    simpa only [Function.comp_def,id_eq,neg_mul] using h
  have H := (he.div_const c).const_mul (d-c)
  simp only [zero_div,mul_zero] at H
  apply squeeze_zero' _ _ H
  · exact Eventually.of_forall fun a => intervalIntegral.integral_nonneg hcd.le fun v hv =>
      (div_pos (Real.exp_pos _) (hc.trans_le hv.1)).le
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
    calc mass c d a ≤ ∫ _v in c..d, Real.exp (-a*c)/c :=
           intervalIntegral.integral_mono_on hcd.le (integrable_profile hc hcd.le _) intervalIntegrable_const
             fun v hv => div_le_div₀ (Real.exp_pos _).le
               (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hv.1 (neg_nonpos.mpr ha))) hc hv.1
         _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]

theorem mass_atBot {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (mass c d) atBot atTop := by
  have he : Tendsto (fun a : ℝ => Real.exp (-a*c)) atBot atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_neg_atBot_atTop.atTop_mul_const hc)
  have H := (he.atTop_div_const (hc.trans hcd)).const_mul_atTop (sub_pos.mpr hcd)
  apply tendsto_atTop_mono' atBot _ H
  filter_upwards [eventually_le_atBot (0:ℝ)] with a ha
  calc (d-c)*(Real.exp (-a*c)/d) = ∫ _v in c..d, Real.exp (-a*c)/d := by
         rw [intervalIntegral.integral_const,smul_eq_mul]
       _ ≤ mass c d a := intervalIntegral.integral_mono_on hcd.le intervalIntegrable_const
         (integrable_profile hc hcd.le _) (fun v hv => div_le_div₀ (Real.exp_pos _).le
           (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv.1 (neg_nonneg.mpr ha))) (hc.trans_le hv.1) hv.2)

theorem response_atBot {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (response c d) atBot (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (mass_atBot hc hcd))

theorem response_atTop {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (response c d) atTop (𝓝 1) := by
  have H := Real.continuous_exp.continuousAt.tendsto.comp (mass_atTop hc hcd).neg
  simpa only [neg_zero,Real.exp_zero,Function.comp_def,response] using H

#print axioms response_zero
#print axioms mass_atTop
#print axioms mass_atBot
#print axioms response_atBot
#print axioms response_atTop

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.VacuumCalibration
