import GaloisForLFunctions.BiScaleUncertainty.SharpCollarCutoffComparison

/-!
# Sharp leading saturation of independent signed-coset allocation

At physical cutoff N, the optimized coefficient misses 4/sqrt(N), with a
uniform inverse-cutoff remainder. The limit coefficient is therefore approached
with exact leading constant four. These statements concern the independent
signed-coset sphere relaxation and its actual grid-source certificates.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem limitingCollarCoefficient_sharp_tail_comparison {n : ℕ} (hn : 6 ≤ n) :
    collarEndpointTailMass n - 8192 / ((n + 2 : ℕ) : ℝ) ≤
      limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n ∧
    limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n ≤
      collarEndpointTailMass n + 12288 / ((n + 2 : ℕ) : ℝ) := by
  have hlim := optimalCoefficient_tendsto.add collarEndpointTailMass_tendsto
  simp only [add_zero] at hlim
  have hlo : PhysicalCollarPartition.optimalCoefficient n + collarEndpointTailMass n -
      8192 / ((n + 2 : ℕ) : ℝ) ≤ limitingCollarCoefficient := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop n] with m hm
    have h := (PhysicalCollarPartition.optimalCoefficient_sharp_cutoff_comparison hm hn).1
    linarith
  have hhi : limitingCollarCoefficient ≤ PhysicalCollarPartition.optimalCoefficient n +
      collarEndpointTailMass n + 12288 / ((n + 2 : ℕ) : ℝ) := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop n] with m hm
    have h := (PhysicalCollarPartition.optimalCoefficient_sharp_cutoff_comparison hm hn).2
    linarith
  constructor <;> linarith

/-- Explicit remainder in the sharp leading allocation law. -/
theorem optimalCoefficient_sharp_leading_error {n : ℕ} (hn : 6 ≤ n) :
    |limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n -
      4 / Real.sqrt ((n + 2 : ℕ) : ℝ)| ≤ 12289 / ((n + 2 : ℕ) : ℝ) := by
  have ht := limitingCollarCoefficient_sharp_tail_comparison hn
  have hm := collarEndpointTailMass_error n
  have hN : 0 ≤ (((n + 2 : ℕ) : ℝ))⁻¹ := by positivity
  apply abs_le.mpr
  simp only [div_eq_mul_inv] at ht hm ⊢
  constructor <;> nlinarith [ht.1, ht.2, hm.1, hm.2]

theorem optimalCoefficient_scaled_leading_error {n : ℕ} (hn : 6 ≤ n) :
    |Real.sqrt ((n + 2 : ℕ) : ℝ) *
      (limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n) - 4| ≤
      12289 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by
  have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hs : 0 < Real.sqrt ((n + 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr hN
  have h := mul_le_mul_of_nonneg_left (optimalCoefficient_sharp_leading_error hn) hs.le
  have hl : Real.sqrt ((n + 2 : ℕ) : ℝ) *
      |limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n -
        4 / Real.sqrt ((n + 2 : ℕ) : ℝ)| =
      |Real.sqrt ((n + 2 : ℕ) : ℝ) *
        (limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n) - 4| := by
    calc
      _ = |Real.sqrt ((n + 2 : ℕ) : ℝ) *
          (limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n -
            4 / Real.sqrt ((n + 2 : ℕ) : ℝ))| := by
        rw [abs_mul, abs_of_nonneg hs.le]
      _ = _ := by
        congr 1
        field_simp [hs.ne']
        ring
  have hr : Real.sqrt ((n + 2 : ℕ) : ℝ) * (12289 / ((n + 2 : ℕ) : ℝ)) =
      12289 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    field_simp [hN.ne', hs.ne']
    nlinarith [Real.sq_sqrt hN.le]
  rw [hl, hr] at h
  exact h

/-- The inverse-square-root leading coefficient is exactly four. -/
theorem optimalCoefficient_sharp_saturation_limit :
    Tendsto (fun n : ℕ => Real.sqrt ((n + 2 : ℕ) : ℝ) *
      (limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n))
      atTop (𝓝 4) := by
  have herr : Tendsto (fun n : ℕ => 12289 / Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_inverse_sqrt_collarCutoff.const_mul 12289)
  have hlo : Tendsto (fun n : ℕ => 4 - 12289 / Real.sqrt ((n + 2 : ℕ) : ℝ))
      atTop (𝓝 4) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub herr)
  have hhi : Tendsto (fun n : ℕ => 4 + 12289 / Real.sqrt ((n + 2 : ℕ) : ℝ))
      atTop (𝓝 4) := by
    simpa only [add_zero] using (tendsto_const_nhds.add herr)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 6] with n hn
    have h := (abs_le.mp (optimalCoefficient_scaled_leading_error hn)).1
    linarith
  · filter_upwards [eventually_ge_atTop 6] with n hn
    have h := (abs_le.mp (optimalCoefficient_scaled_leading_error hn)).2
    linarith

/-- The leading allocation law gives a quantitative actual grid-source lower bound. -/
theorem sharpCollar_source_lower_bound {n : ℕ} (hn : 6 ≤ n)
    (f : SmoothLogarithmicGridSource n) :
    limitingCollarCoefficient - 4 / Real.sqrt ((n + 2 : ℕ) : ℝ) -
      12289 / ((n + 2 : ℕ) : ℝ) ≤
      biScaleLevyEnergy f.1.1 / RHTower.ArchimedeanAnomaly.autocorr f.1.1 0 := by
  have h := (abs_le.mp (optimalCoefficient_sharp_leading_error hn)).2
  have hf := optimalCoefficient_le_normalized_energy n f
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty
