import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.Uniform
import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.EntropyBoundaryAsymptotics

/-! # Local mass of a fixed arithmetic energy-gap window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Set MeasureTheory Topology

theorem collisionMass_sublinear :
    Tendsto (fun h : Ioi (0:ℝ) => collisionMass h/h.val) criticalApproach (𝓝 0) := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have hl := collisionMass_quadratic_limit.mul (hv.mono_right nhdsWithin_le_nhds)
  rw [mul_zero] at hl
  apply hl.congr
  intro h
  have hh : h.val ≠ 0 := (show 0 < h.val from h.property).ne'
  field_simp [hh]

private theorem moving_cutoff_discrepancy (a : ℝ) :
    Tendsto (fun h : Ioi (0:ℝ) => (gapCDF h (h.val*a)-laplaceCDF (h.val*a))/h.val)
      criticalApproach (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ collisionMass_sublinear
  intro h
  have hh : 0 < h.val := h.property
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hh]
  exact div_le_div_of_nonneg_right (uniform_gap_cdf_error h _) hh.le

private theorem moving_reference_slope (a : ℝ) :
    Tendsto (fun h : Ioi (0:ℝ) => (laplaceCDF (h.val*a)-laplaceCDF 0)/h.val)
      criticalApproach (𝓝 (a/2)) := by
  have hd : HasDerivAt laplaceCDF (1/2) (0:ℝ) := by
    simpa only [_root_.RHTower.mobiusCriticalLaplaceGapDensity,abs_zero,neg_zero,Real.exp_zero,mul_one] using laplaceCDF_derivative 0
  have ha : HasDerivAt (fun x : ℝ => x*a) a 0 := by
    have hx := (hasDerivAt_id (0:ℝ)).mul_const a
    rw [one_mul] at hx
    exact hx
  have H : HasDerivAt (fun x : ℝ => laplaceCDF (x*a)) (a/2) 0 := by
    have hd' : HasDerivAt laplaceCDF (1/2) (0*a) := by simpa only [zero_mul] using hd
    have hx := hd'.comp 0 ha
    rw [show (1/2:ℝ)*a = a/2 by ring] at hx
    exact hx
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  apply ((GaloisForLFunctions.HTGeometry.Quantum.FermiGraph.tendsto_right_difference_quotient H).comp hv).congr
  intro h
  change (laplaceCDF (h.val*a)-laplaceCDF (0*a))/h.val = _
  rw [zero_mul]

private theorem moving_gap_slope (a : ℝ) :
    Tendsto (fun h : Ioi (0:ℝ) => (gapCDF h (h.val*a)-laplaceCDF 0)/h.val)
      criticalApproach (𝓝 (a/2)) := by
  have hl := (moving_cutoff_discrepancy a).add (moving_reference_slope a)
  rw [zero_add] at hl
  apply hl.congr
  intro h
  ring

/-- At fixed physical resolution, each interval of log ratios carries asymptotic mass h times half its length. -/
theorem fixed_gap_window_limit {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun h : Ioi (0:ℝ) =>
      (sampledGapLaw (excessDamping h) (1/2) (excessDamping_gt h) : Measure ℝ).real (Ioc a b)/h.val)
      criticalApproach (𝓝 ((b-a)/2)) := by
  have hl := (moving_gap_slope b).sub (moving_gap_slope a)
  rw [show b/2-a/2 = (b-a)/2 by ring] at hl
  apply hl.congr
  intro h
  have hh : 0 < h.val := h.property
  have he : (fun q => h.val/2*gapFrequency q) ⁻¹' Ioc (h.val*a) (h.val*b) =
      (fun q => (1/2:ℝ)*gapFrequency q) ⁻¹' Ioc a b := by
    ext q
    have hx : h.val/2*gapFrequency q = h.val*((1/2:ℝ)*gapFrequency q) := by ring
    simp only [mem_preimage,mem_Ioc,hx,mul_lt_mul_iff_right₀ hh,mul_le_mul_iff_right₀ hh]
  have hr : (criticalGapLaw h : Measure ℝ).real (Ioc (h.val*a) (h.val*b)) =
      (sampledGapLaw (excessDamping h) (1/2) (excessDamping_gt h) : Measure ℝ).real (Ioc a b) := by
    change ((Measure.map _ _) _).toReal = ((Measure.map _ _) _).toReal
    rw [Measure.map_apply Measurable.of_discrete measurableSet_Ioc,
      Measure.map_apply Measurable.of_discrete measurableSet_Ioc,he]
  rw [← hr,real_band_eq_cdf_sub _ (mul_le_mul_of_nonneg_left hab h.property.le)]
  change (gapCDF h (h.val*b)-laplaceCDF 0)/h.val-(gapCDF h (h.val*a)-laplaceCDF 0)/h.val =
    (gapCDF h (h.val*b)-gapCDF h (h.val*a))/h.val
  ring

#print axioms collisionMass_sublinear
#print axioms fixed_gap_window_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
