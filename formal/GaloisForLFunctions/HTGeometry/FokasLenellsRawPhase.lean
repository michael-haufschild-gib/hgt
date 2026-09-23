import GaloisForLFunctions.HTGeometry.FokasLenellsRawFirstScattering

/-!
# An exact nonsingular remainder for the oscillatory scattering phase

A compact interval average of the phase gives its first divided difference
without any division. The identity remains valid at zero frequency and has
a unit norm bound. It supplies the cubic kernel of the original spectral
scattering equation.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawPhaseAverage (r x : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, FDNLS.staggerPhase r (t*x)

theorem continuous_rawPhaseAverage_parameters :
    Continuous (fun p : ℝ × ℝ => rawPhaseAverage p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry FDNLS.staggerPhase
  fun_prop

theorem rawPhaseAverage_bound (r x : ℝ) : ‖rawPhaseAverage r x‖ ≤ 1 := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 1) (fun t _ => (FDNLS.norm_staggerPhase r (t*x)).le)
  simpa only [rawPhaseAverage,sub_zero,abs_one,mul_one] using hh

theorem rawPhaseAverage_zero_frequency (x : ℝ) : rawPhaseAverage 0 x = 1 := by
  simp [rawPhaseAverage,FDNLS.staggerPhase]

theorem rawPhaseAverage_zero_position (r : ℝ) : rawPhaseAverage r 0 = 1 := by
  simp [rawPhaseAverage,FDNLS.staggerPhase]

private theorem phase_segment_derivative (r x t : ℝ) :
    HasDerivAt (fun s : ℝ => FDNLS.staggerPhase r (s*x))
      ((-I*(r : ℂ)*(x : ℂ))*FDNLS.staggerPhase r (t*x)) t := by
  have hh := (FDNLS.hasDerivAt_staggerPhase r (t*x)).scomp t ((hasDerivAt_id t).mul_const x)
  convert! hh using 1
  simp only [one_mul,Complex.real_smul]
  ring

/-- An exact integral remainder, with no nonzero-frequency premise. -/
theorem staggerPhase_sub_one_factor (r x : ℝ) :
    FDNLS.staggerPhase r x-1 = (-I*(r : ℂ)*(x : ℂ))*rawPhaseAverage r x := by
  have hc : Continuous (fun t : ℝ => (-I*(r : ℂ)*(x : ℂ))*FDNLS.staggerPhase r (t*x)) := by
    unfold FDNLS.staggerPhase
    fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => phase_segment_derivative r x t) (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hh
  simpa only [one_mul,zero_mul,FDNLS.staggerPhase,Complex.ofReal_zero,mul_zero,Complex.exp_zero,
    rawPhaseAverage] using hh.symm

/-- The averaged phase tends to one through zero in the actual real spectral parameter. -/
theorem rawPhaseAverage_tendsto_zero (x : ℝ) :
    Tendsto (fun r : ℝ => rawPhaseAverage r x) (𝓝 0) (𝓝 1) := by
  have hp : Continuous (fun r : ℝ => (r,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_rawPhaseAverage_parameters.comp hp).tendsto 0
  simpa only [Function.comp_def,rawPhaseAverage_zero_frequency] using hh

/-- The two original scattering phases have an exact quadratic spectral remainder. -/
theorem staggerPhase_square_sub_one_factor (k x : ℝ) :
    FDNLS.staggerPhase (2*k^(2 : ℕ)) x-1 =
      (k : ℂ)^(2 : ℕ)*(-2*I*(x : ℂ))*rawPhaseAverage (2*k^(2 : ℕ)) x := by
  rw [staggerPhase_sub_one_factor]
  push_cast
  ring

theorem staggerPhase_neg_square_sub_one_factor (k x : ℝ) :
    FDNLS.staggerPhase (-(2*k^(2 : ℕ))) x-1 =
      (k : ℂ)^(2 : ℕ)*(2*I*(x : ℂ))*rawPhaseAverage (-(2*k^(2 : ℕ))) x := by
  rw [staggerPhase_sub_one_factor]
  push_cast
  ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
