import GaloisForLFunctions.HTGeometry.FokasLenellsRawEndpoints

/-!
# Uniform approach to zero spectral frequency

The total variation estimate gives a position-independent bound for the
distance from the identity evolution. Passing it to both infinite endpoints
proves continuity through k = 0 directly for the original scattering flow.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- A single explicit error controls the complete line and both scattering endpoints. -/
def rawZeroError (q : SchwartzMap ℝ ℂ) (k : ℝ) : ℝ :=
  Real.exp (|k| * rawInteractionMass q)*|k| * rawInteractionMass q

theorem rawZeroError_nonneg (q : SchwartzMap ℝ ℂ) (k : ℝ) : 0 ≤ rawZeroError q k :=
  mul_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg k)) (rawInteractionMass_nonneg q)

theorem rawZeroError_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (rawZeroError q) (𝓝 0) (𝓝 0) := by
  have hh : Continuous (rawZeroError q) := by unfold rawZeroError; fun_prop
  simpa only [rawZeroError,abs_zero,zero_mul,Real.exp_zero,mul_zero] using hh.tendsto 0

/-- The original solution approaches its initial vector uniformly over the entire spatial line. -/
theorem rawInteractionSolution_sub_initial_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawInteractionSolution q k v x-v‖ ≤ ‖v‖*rawZeroError q k := by
  have he := rawInteractionSolution_equation q k v x
  change rawInteractionSolution q k v x = v+∫ s in (0 : ℝ)..x, rawInteractionDerivative q k v s at he
  rw [he,add_sub_cancel_left]
  have h1 : ‖∫ s in (0 : ℝ)..x, rawInteractionDerivative q k v s‖ ≤
      ∫ s : ℝ, ‖rawInteractionDerivative q k v s‖ :=
    intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral (rawInteractionDerivative_integrable q k v).norm
        (Eventually.of_forall fun s => norm_nonneg (rawInteractionDerivative q k v s)))
  exact h1.trans ((integral_norm_rawInteractionDerivative q k v).trans_eq (by unfold rawZeroError; ring))

theorem rawInteractionSolution_tendsto_zero_frequency (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawInteractionSolution q k v x) (𝓝 0) (𝓝 v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _) (fun k => rawInteractionSolution_sub_initial_bound q k v x)
  simpa only [mul_zero] using (rawZeroError_tendsto q).const_mul ‖v‖

theorem continuousAt_rawInteractionSolution_zero_frequency (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    ContinuousAt (fun k => rawInteractionSolution q k v x) 0 := by
  simpa only [ContinuousAt,rawInteractionSolution_zero_frequency] using rawInteractionSolution_tendsto_zero_frequency q v x

/-- Sending position to infinity preserves the same first-order error, on both sides. -/
theorem rawAsymptoticVector_sub_initial_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    ‖rawAsymptoticVector q k v left-v‖ ≤ ‖v‖*rawZeroError q k := by
  apply le_of_tendsto ((rawOrientedSolution_tendsto q k v left).sub_const v).norm
  exact Eventually.of_forall fun x => rawInteractionSolution_sub_initial_bound q k v (if left then -x else x)

theorem rawAsymptoticVector_tendsto_zero_frequency (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    Tendsto (fun k => rawAsymptoticVector q k v left) (𝓝 0) (𝓝 v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _) (fun k => rawAsymptoticVector_sub_initial_bound q k v left)
  simpa only [mul_zero] using (rawZeroError_tendsto q).const_mul ‖v‖

theorem continuousAt_rawAsymptoticVector_zero_frequency (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    ContinuousAt (fun k => rawAsymptoticVector q k v left) 0 := by
  simpa only [ContinuousAt,rawAsymptoticVector_zero_frequency] using rawAsymptoticVector_tendsto_zero_frequency q v left

end
end GaloisForLFunctions.HTGeometry.FokasLenells
