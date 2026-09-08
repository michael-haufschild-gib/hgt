import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspMeanEnergy

/-! Native energy excludes the constructed growing coefficient and fixes the exact source-tail flux. -/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse
noncomputable section

/-- The original native Hilbert norm excludes the actual growing cusp coefficient
at every Xi occurrence, with no critical-line or boundary-flux premise. -/
theorem limitingCoefficient_growing_zero (q : XiZeroCopy) (branch : Bool) :
    limitingCoefficient q branch true = 0 := by
  by_contra hB
  let c : ℝ := ‖limitingCoefficient q branch true‖/2
  have hc : 0 < c := half_pos (norm_pos_iff.mpr hB)
  have hg : ∀ᶠ y : ℝ in atTop,
      c ≤ ‖responseMean q branch y/(y:ℂ)^(root q branch true)‖ := by
    have h := (responseMean_dominant_coefficient q branch).norm.eventually
      (Ioi_mem_nhds (show c < ‖limitingCoefficient q branch true‖ by dsimp [c]; linarith [norm_pos_iff.mpr hB]))
    exact h.mono (fun y hy => hy.le)
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hg
  let T : ℝ := max 2 Y
  have hi := (responseMean_density_integrable q branch).mono_set
    (Ioi_subset_Ioi (le_max_left (2:ℝ) Y))
  have hr : 1 ≤ (root q branch true).re := by
    have hb := (physicalRate_re_bounds q branch).2
    norm_num [root]
    linarith
  have hconst : Integrable (fun _ : ℝ => c^2) (volume.restrict (Ioi T)) := by
    apply hi.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy2 : 2 < y := lt_of_le_of_lt (le_max_left (2:ℝ) Y) hy
    have hp : 0 < y := by linarith
    have hlarge : 1 ≤ y := by linarith
    have hpow : y ≤ ‖(y:ℂ)^(root q branch true)‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
      calc
        y = y^(1:ℝ) := (Real.rpow_one y).symm
        _ ≤ y^((root q branch true).re) := Real.rpow_le_rpow_of_exponent_le hlarge hr
    have hpn : 0 < ‖(y:ℂ)^(root q branch true)‖ :=
      lt_of_lt_of_le hp hpow
    have hratio := hY y ((le_max_right (2:ℝ) Y).trans hy.le)
    rw [norm_div] at hratio
    have hm : c*y ≤ ‖responseMean q branch y‖ :=
      (mul_le_mul_of_nonneg_left hpow hc.le).trans ((le_div_iff₀ hpn).mp hratio)
    have hsq := (sq_le_sq₀ (mul_nonneg hc.le hp.le) (norm_nonneg _)).mpr hm
    rw [mul_pow] at hsq
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg c)]
    exact (le_div_iff₀ (sq_pos_of_pos hp)).mpr hsq
  haveI : IsFiniteMeasure (volume.restrict (Ioi T)) :=
    (integrable_const_iff_isFiniteMeasure (pow_ne_zero 2 hc.ne')).mp hconst
  have hf := measure_lt_top (volume.restrict (Ioi T)) univ
  simp only [Measure.restrict_apply_univ,Real.volume_Ioi,lt_self_iff_false] at hf

/-- The actual Wronskian limit on the complementary testing power is zero,
proved from the original native norm rather than imposed as boundary data. -/
theorem limitingFlux_first_zero (q : XiZeroCopy) (branch : Bool) :
    limitingFlux q branch false = 0 := by
  have h := limitingCoefficient_growing_zero q branch
  simpa [limitingCoefficient,div_eq_zero_iff,rootGap_ne_zero q branch] using h

/-- Exact source-dependent cusp boundary constraint obeyed by the original native energy response. -/
theorem responseFlux_first_eq_neg_source_tail (q : XiZeroCopy) (branch : Bool)
    {y : ℝ} (hy : 3 < y) :
    responseFlux q branch false y = -(∫ t in Ioi y, fluxSource q branch false t) := by
  rw [responseFlux_eq_limit_sub_tail q branch false hy,limitingFlux_first_zero,zero_sub]

/-- The native response's exact decomposition retains its surviving homogeneous
coefficient and both source tails after the growing coefficient is eliminated. -/
theorem responseMean_native_decomposition (q : XiZeroCopy) (branch : Bool)
    {y : ℝ} (hy : 3 < y) :
    responseMean q branch y =
      (y:ℂ)^(root q branch false)*limitingCoefficient q branch false+
      ((y:ℂ)^(root q branch false)*(∫ t in Ioi y, fluxSource q branch true t)-
        (y:ℂ)^(root q branch true)*(∫ t in Ioi y, fluxSource q branch false t))/rootGap q branch := by
  rw [responseMean_limit_source q branch hy,limitingCoefficient_growing_zero,mul_zero,add_zero]

end
end RHTower.D4BMCuspResponse
