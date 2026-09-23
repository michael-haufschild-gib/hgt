import GaloisForLFunctions.HTGeometry.FokasLenellsRegularOrigin

/-!
# The first positive-coordinate transmission coefficient

The original scattering matrix's quadratic coefficient becomes the
first positive-z coefficient of each actual regularized transmission.
This coefficient determines the finite part after division by transmission.
-/

open Complex Matrix MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The gauge preserves the actual transmission entries on the positive spectral ray. -/
theorem regularTransmission_exp_eq_raw (q : SchwartzMap ℝ ℂ) (κ : ℝ) (i : Fin 2) :
    regularScatteringMatrix q ((Real.exp κ)^(2 : ℕ)) i i = rawScatteringMatrix q (Real.exp κ) i i := by
  rw [regularScatteringMatrix, uniformizedScatteringMatrix_amplitudes, rawScatteringMatrix_exp_eq]
  fin_cases i <;> rfl

private theorem regular_transmission_sqrt (q : SchwartzMap ℝ ℂ) (z : ℝ) (hz : 0 < z) (i : Fin 2) :
    regularScatteringMatrix q z i i = rawScatteringMatrix q (Real.sqrt z) i i := by
  have hh := regularTransmission_exp_eq_raw q (Real.log (Real.sqrt z)) i
  rwa [Real.exp_log (Real.sqrt_pos.mpr hz), Real.sq_sqrt hz.le] at hh

/-- Both actual transmission entries have a right derivative determined by the original quadratic scattering coefficient. -/
theorem regularTransmission_diagonal_right_quotient_tendsto (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Tendsto (fun z : ℝ => (regularScatteringMatrix q z i i - 1)/(z : ℂ))
      (𝓝[>] 0) (𝓝 (rawScatteringQuadraticCoefficient q i i)) := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  have hk := (Complex.continuous_ofReal.tendsto 0).comp hs
  have hc : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i i) := by fun_prop
  have hR := (hc.tendsto (rawScatteringCubicCoefficient q)).comp
    ((rawScatteringCubicRemainder_tendsto_zero q).comp hs)
  have hconst : Tendsto (fun _ : ℝ => rawScatteringQuadraticCoefficient q i i)
      (𝓝[>] 0) (𝓝 (rawScatteringQuadraticCoefficient q i i)) := tendsto_const_nhds
  have hh := hconst.add (hk.mul hR)
  change Tendsto (fun z : ℝ => rawScatteringQuadraticCoefficient q i i +
    (Real.sqrt z : ℂ)*rawScatteringCubicRemainder q (Real.sqrt z) i i)
    (𝓝[>] 0) (𝓝 (rawScatteringQuadraticCoefficient q i i + (0 : ℂ)*rawScatteringCubicCoefficient q i i)) at hh
  simp only [zero_mul, add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [regular_transmission_sqrt q z hz i, rawScatteringMatrix_cubic_factor]
  have hsquare : (Real.sqrt z : ℂ)^(2 : ℕ) = (z : ℂ) := by exact_mod_cast Real.sq_sqrt hz.le
  have hroot : (Real.sqrt z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hz))
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq]
  rw [← hsquare]
  field_simp
  ring

/-- The upper transmission's first coefficient is the mixed derivative moment. -/
theorem regularTransmission_upper_right_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => (regularScatteringMatrix q z 1 1 - 1)/(z : ℂ))
      (𝓝[>] 0) (𝓝 (rawMixedTotal q)) := by
  have hh := regularTransmission_diagonal_right_quotient_tendsto q 1
  have he : rawScatteringQuadraticCoefficient q 1 1 = rawMixedTotal q := by
    rw [rawScatteringQuadraticCoefficient_eq]
    rfl
  rwa [he] at hh

/-- The lower transmission has the opposite mixed-moment first coefficient. -/
theorem regularTransmission_lower_right_quotient_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => (regularScatteringMatrix q z 0 0 - 1)/(z : ℂ))
      (𝓝[>] 0) (𝓝 (-rawMixedTotal q)) := by
  have hh := regularTransmission_diagonal_right_quotient_tendsto q 0
  have he : rawScatteringQuadraticCoefficient q 0 0 = -rawMixedTotal q := by
    rw [rawScatteringQuadraticCoefficient_eq]
    rfl
  rwa [he] at hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
