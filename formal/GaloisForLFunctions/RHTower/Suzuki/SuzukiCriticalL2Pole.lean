import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalPolePointwise
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2PrimaryVariation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalPolePairing

/-!
# Compact L² testing of the critical pole

A compact correlation cutoff and the primary-mass bound give dominated convergence
for the growing pole. Adding that finite limit to the primary extended variation
recovers the signed source cusp without a smoothness or finite-energy premise.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section

private theorem window_const_integrable (A R : ℝ) :
    Integrable ((Ioo (0 : ℝ) A).indicator (fun _ => R)) := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  exact continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self

private theorem pole_test_bound {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {A u omega : ℝ} (_hA : 0 < A) (hu : 0 ≤ u)
    (hcut : ∀ t, A ≤ t → autocorr f t = 0)
    (homega : 0 < omega) (homega2 : omega ≤ 1/2) (t : ℝ) :
    ‖autocorr f (u+t) * suzukiCriticalPoleDensity omega t‖ ≤
      (Ioo (0 : ℝ) A).indicator
        (fun _ => autocorr f 0 * suzukiCriticalPrimaryMass omega * Real.exp (A/2)) t := by
  have hR : 0 ≤ autocorr f 0 := by rw [autocorr_zero_eq_norm_toLp_sq hf]; positivity
  have hM : 0 ≤ suzukiCriticalPrimaryMass omega := by
    rw [← integral_suzukiCriticalPrimaryDensity homega (by linarith : omega < 5/2)]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (suzukiCriticalPrimaryDensity_pos homega hr).le
  by_cases ht : 0 < t
  · by_cases htA : t < A
    · rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) A from ⟨ht,htA⟩)]
      have hP := suzukiCriticalPoleDensity_bounds homega homega2 ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP.1]
      calc
        _ ≤ autocorr f 0 * (suzukiCriticalPrimaryMass omega * Real.exp (t/2)) :=
          mul_le_mul (abs_autocorr_le_zero_of_memLp hf (u+t)) hP.2 hP.1 hR
        _ ≤ autocorr f 0 * (suzukiCriticalPrimaryMass omega * Real.exp (A/2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by linarith)) hM) hR
        _ = _ := by ring
    · have hnot : t ∉ Ioo (0 : ℝ) A := fun h => htA h.2
      rw [indicator_of_notMem hnot, hcut (u+t) (by linarith), zero_mul, norm_zero]
  · have hnot : t ∉ Ioo (0 : ℝ) A := fun h => ht h.1
    rw [indicator_of_notMem hnot, suzukiCriticalPoleDensity_eq_zero_of_nonpos (le_of_not_gt ht),
      mul_zero, norm_zero]

/-- The pole density is absolutely integrable against every compact L² correlation. -/
theorem integrable_suzukiCriticalPoleCusp_integrand_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) {u omega : ℝ} (hu : 0 ≤ u)
    (homega : 0 < omega) (homega2 : omega ≤ 1/2) :
    Integrable (fun t => autocorr f (u+t) * suzukiCriticalPoleDensity omega t) := by
  obtain ⟨A,hA,hcut⟩ := exists_pos_autocorr_cutoff hfc
  apply (window_const_integrable A
    (autocorr f 0 * suzukiCriticalPrimaryMass omega * Real.exp (A/2))).mono'
  · exact (((continuous_autocorr_of_memLp hf).measurable.comp
      (measurable_const.add measurable_id)).mul
        (measurable_suzukiCriticalPoleDensity omega)).aestronglyMeasurable
  · exact Eventually.of_forall (pole_test_bound hf hA hu hcut homega homega2)

/-- The growing pole survives the critical limit on every compact L² source. -/
theorem tendsto_suzukiCriticalPoleCusp_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun omega => suzukiCriticalPoleCusp f omega u) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi 0, autocorr f (u+t) * Real.exp (t/2))) := by
  obtain ⟨A,hA,hcut⟩ := exists_pos_autocorr_cutoff hfc
  have hR : 0 ≤ autocorr f 0 := by rw [autocorr_zero_eq_norm_toLp_sq hf]; positivity
  have hM : ∀ᶠ omega : ℝ in 𝓝[>] 0, suzukiCriticalPrimaryMass omega < 2 :=
    (tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ)<2))
  have ho : ∀ᶠ omega : ℝ in 𝓝[>] 0, omega < 1/2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  apply tendsto_integral_filter_of_dominated_convergence
    ((Ioo (0 : ℝ) A).indicator (fun _ => autocorr f 0 * 2 * Real.exp (A/2)))
  · exact Eventually.of_forall fun omega =>
      (((continuous_autocorr_of_memLp hf).measurable.comp
        (measurable_const.add measurable_id)).mul
          (measurable_suzukiCriticalPoleDensity omega)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, ho, hM] with omega homega ho hM
    exact Eventually.of_forall fun t => (pole_test_bound hf hA hu hcut homega ho.le t).trans (by
      by_cases ht : t ∈ Ioo (0 : ℝ) A
      · rw [indicator_of_mem ht, indicator_of_mem ht]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM.le hR)
          (Real.exp_pos _).le
      · rw [indicator_of_notMem ht, indicator_of_notMem ht])
  · exact (window_const_integrable A _).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (tendsto_suzukiCriticalPoleDensity ht).const_mul (autocorr f (u+t))

/-- The signed source cusp is absolutely integrable for compact L² sources. -/
theorem integrableOn_suzukiCriticalSourceCusp_integrand_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) {u omega : ℝ} (hu : 0 ≤ u)
    (homega : 0 < omega) (homega2 : omega ≤ 1/2) :
    IntegrableOn (fun t => autocorr f (u+t) * suzukiCriticalSourceDensity omega t) (Ioi 0) := by
  have hB := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp hf homega
    (by linarith : omega < 5/2) u
  have hP := (integrable_suzukiCriticalPoleCusp_integrand_of_memLp hf hfc hu homega homega2).integrableOn (s := Ioi 0)
  apply (hB.sub (hP.const_mul (2*omega))).congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.sub_apply]
  rw [suzukiCriticalSourceDensity_eq omega ht]
  ring

/-- The signed cusp splits exactly into its primary and pole contributions. -/
theorem suzukiCriticalSourceCusp_eq_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) {u omega : ℝ} (hu : 0 ≤ u)
    (homega : 0 < omega) (homega2 : omega ≤ 1/2) :
    suzukiCriticalSourceCusp f omega u = suzukiCriticalPrimaryCusp f omega u -
      2*omega*suzukiCriticalPoleCusp f omega u := by
  have hB := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp hf homega
    (by linarith : omega < 5/2) u
  have hP := (integrable_suzukiCriticalPoleCusp_integrand_of_memLp hf hfc hu homega homega2).integrableOn (s := Ioi 0)
  unfold suzukiCriticalSourceCusp suzukiCriticalPrimaryCusp suzukiCriticalPoleCusp
  calc
    _ = ∫ t in Ioi 0, autocorr f (u+t) * suzukiCriticalPrimaryDensity omega t -
        (2*omega)*(autocorr f (u+t) * suzukiCriticalPoleDensity omega t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [suzukiCriticalSourceDensity_eq omega ht]
      ring
    _ = _ := by rw [integral_sub hB (hP.const_mul _), integral_const_mul]

/-- Every nonnegative translated signed cusp converges to its L² correlation. -/
theorem tendsto_suzukiCriticalSourceCusp_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun omega => suzukiCriticalSourceCusp f omega u) (𝓝[>] 0)
      (𝓝 (autocorr f u)) := by
  have hp := tendsto_suzukiCriticalPoleCusp_of_memLp hf hfc hu
  have hi : Tendsto (fun omega : ℝ => omega) (𝓝[>] 0) (𝓝 0) := continuousWithinAt_id
  have h := ((tendstoUniformly_suzukiCriticalPrimaryCusp_of_memLp hf).tendsto_at u).sub
    ((hi.const_mul 2).mul hp)
  simp only [mul_zero, zero_mul, sub_zero] at h
  apply h.congr'
  have ho : ∀ᶠ omega : ℝ in 𝓝[>] 0, omega < 1/2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
  exact (suzukiCriticalSourceCusp_eq_of_memLp hf hfc hu homega ho.le).symm

/-- The signed cusp has an extended first variation, with its growing pole retained. -/
theorem tendsto_suzukiCriticalSourceCusp_extended_firstVariation {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) :
    Tendsto (fun omega : ℝ => (((autocorr f 0-suzukiCriticalSourceCusp f omega 0) /
      omega : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 ((suzukiCriticalLimitingCompensatedEnergy
        (fun t => autocorr f 0-autocorr f t) : EReal) +
        ((((Complex.digamma ((5/4 : ℝ) : ℂ)).re-Real.log Real.pi) * autocorr f 0 +
          2 * ∫ t in Ioi 0, autocorr f t * Real.exp (t/2)) : ℝ))) := by
  have hp := tendsto_suzukiCriticalPoleCusp_of_memLp hf hfc (le_refl (0 : ℝ))
  simp only [zero_add] at hp
  have hpE := continuous_coe_real_ereal.continuousAt.tendsto.comp (hp.const_mul 2)
  have h := (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))).tendsto.comp
      ((tendsto_suzukiCriticalPrimaryCusp_extended_firstVariation hf).prodMk_nhds hpE)
  have hlim : Tendsto (fun omega : ℝ =>
      ((((autocorr f 0-suzukiCriticalPrimaryCusp f omega 0)/omega : ℝ) : EReal) +
        ((2*suzukiCriticalPoleCusp f omega 0 : ℝ) : EReal))) (𝓝[>] 0)
      (𝓝 ((suzukiCriticalLimitingCompensatedEnergy
        (fun t => autocorr f 0-autocorr f t) : EReal) +
        ((((Complex.digamma ((5/4 : ℝ) : ℂ)).re-Real.log Real.pi)*autocorr f 0 +
          2 * ∫ t in Ioi 0, autocorr f t * Real.exp (t/2)) : ℝ))) := by
    dsimp only [Function.comp] at h
    simpa only [add_assoc, ← EReal.coe_add] using h
  apply hlim.congr'
  have ho : ∀ᶠ omega : ℝ in 𝓝[>] 0, omega < 1/2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
  change 0 < omega at homega
  rw [suzukiCriticalSourceCusp_eq_of_memLp hf hfc (le_refl (0 : ℝ)) homega ho.le, ← EReal.coe_add]
  congr 1
  field_simp [ne_of_gt homega]
  ring

end
end RHTower
