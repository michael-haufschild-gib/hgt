import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.MovingCutoff

/-! # The limiting conditional law at every prime aperture -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace

/-- Finite-window energy law at drift -c, expressed in the original pole units. -/
def cutoffLaw (c : ℝ) : ProbabilityMeasure ℝ :=
  (Window.energy_window_limit (-c)).choose.map (f := fun x : ℝ => c*x)
    (measurable_const.mul measurable_id).aemeasurable

theorem charFun_cutoffLaw (c t : ℝ) :
    charFun (cutoffLaw c : Measure ℝ) t = limitTransform c ((t:ℂ)*Complex.I) := by
  change charFun (((Window.energy_window_limit (-c)).choose : Measure ℝ).map (fun x => c*x)) t = _
  rw [charFun_map_mul,
    (Window.energy_window_limit (-c)).choose_spec.1,limitTransform,criticalEulerCarrier,criticalEulerCarrier,
    ← Complex.exp_sub,Complex.ofReal_neg,Complex.ofReal_mul]
  have he : -(c:ℂ)+((c:ℂ)*(t:ℂ))*Complex.I = (c:ℂ)*((t:ℂ)*Complex.I-1) := by ring
  change Complex.exp (criticalEulerExponent (-(c:ℂ)+((c:ℂ)*(t:ℂ))*Complex.I)-criticalEulerExponent (-(c:ℂ))) = _
  rw [he]

/-- Weak limit of the unrestricted orientation energy conditioned on its largest marked prime. -/
theorem conditioned_weak_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (conditionalLaw c) criticalApproach (𝓝 (cutoffLaw c)) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  rw [charFun_cutoffLaw]
  exact ((conditioned_transform_limit hc ((t:ℂ)*Complex.I)).congr
    (fun h => (charFun_conditionalLaw c h t).symm)).comp hu

private theorem real_exponent (v : ℝ) : criticalEulerExponent (-(v:ℂ)) = -(ein v:ℂ) := by
  have H := Window.negative_profile_real (v/2)
  have ha : -2*((v/2:ℝ):ℂ) = -(v:ℂ) := by push_cast; ring
  rw [ha] at H
  have he : (fun t : ℝ => (1-Real.exp (-2*(v/2)*t))/t) = scaledEinProfile v := by
    funext t
    by_cases ht : t = 0
    · simp [ht,scaledEinProfile]
    · rw [scaledEinProfile,if_neg ht,show -2*(v/2) = -v by ring,neg_mul]
  rw [he,scaledEinProfile_eq,intervalIntegral.integral_const_mul] at H
  have hi : v*(∫ t in (0:ℝ)..1, einProfile (v*t)) = ein v := by
    by_cases hv : v = 0
    · simp [hv,ein]
    · rw [intervalIntegral.integral_comp_mul_left einProfile hv,mul_zero,mul_one,smul_eq_mul,
        ← mul_assoc,mul_inv_cancel₀ hv,one_mul,ein]
  rw [hi] at H
  change -criticalEulerExponent (-(v:ℂ)) = (ein v:ℂ) at H
  simpa only [neg_neg] using congrArg Neg.neg H

/-- Real conditional Laplace transform for every tilt, including those crossing the partition pole. -/
theorem all_real_laplace {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Tendsto (fun h => jointReading c t h/jointReading c 0 h) criticalApproach
      (𝓝 (Real.exp (ein c-ein ((1+t)*c)))) := by
  have H := conditioned_transform_limit hc (-(t:ℂ))
  have he : limitTransform c (-(t:ℂ)) = (Real.exp (ein c-ein ((1+t)*c)):ℂ) := by
    have ha : (c:ℂ)*(-(t:ℂ)-1) = -(((1+t)*c:ℝ):ℂ) := by push_cast; ring
    rw [limitTransform,criticalEulerCarrier,criticalEulerCarrier,ha,real_exponent,real_exponent,
      ← Complex.exp_sub,Complex.ofReal_exp,Complex.ofReal_sub]
    congr 1
    ring
  rw [he] at H
  have hr := (Complex.continuous_re.tendsto _).comp H
  simpa only [Function.comp_def,laplace_reading,Complex.ofReal_re] using hr

#print axioms charFun_cutoffLaw
#print axioms conditioned_weak_limit
#print axioms all_real_laplace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime
