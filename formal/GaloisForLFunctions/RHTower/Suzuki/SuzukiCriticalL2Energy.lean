import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalExtendedEnergy
import GaloisForLFunctions.BiScaleUncertainty.PhysicalTranslationContinuity
import GaloisForLFunctions.RHTower.EvenSectorLevyKreinRigidity

/-!
# Critical Suzuki energy for every real L² source

Autocorrelation is a continuous matrix coefficient of the physical translation
isometries. Its nonnegative bounded deficit therefore has the exact extended
critical energy limit, including infinite energy. No compact support, smoothness,
or finite Lévy energy is required.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace
open GaloisForLFunctions.BiScaleUncertainty.SobolevShear

namespace RHTower
open ArchimedeanAnomaly ArchimedeanExactForm
noncomputable section

/-- Autocorrelation depends only on the almost-everywhere source class. -/
theorem autocorr_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) (t : ℝ) :
    autocorr f t = autocorr g t := by
  unfold autocorr
  apply integral_congr_ae
  filter_upwards [hfg, ae_physicalTranslate_pullback t hfg] with u hu hut
  rw [hu, hut]

/-- The ordinary correlation integral is the translation matrix coefficient. -/
theorem autocorr_eq_inner_physicalTranslation (q : Velocity) (t : ℝ) :
    autocorr q t = ⟪q, physicalTranslation t q⟫ := by
  rw [autocorr, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_physicalTranslation t q] with u hu
  rw [hu, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

/-- Raw L² representatives give the same matrix coefficient as their Hilbert class. -/
theorem autocorr_eq_inner_toLp {f : ℝ → ℝ} (hf : MemLp f 2 volume) (t : ℝ) :
    autocorr f t = ⟪hf.toLp f, physicalTranslation t (hf.toLp f)⟫ := by
  rw [← autocorr_eq_inner_physicalTranslation]
  exact autocorr_congr_ae hf.coeFn_toLp.symm t

/-- Strong continuity of physical translations gives continuous L² autocorrelations. -/
theorem continuous_autocorr_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Continuous (autocorr f) := by
  have h := Continuous.inner (𝕜 := ℝ)
    (continuous_const : Continuous (fun _ : ℝ => hf.toLp f))
    (continuous_physicalTranslation (hf.toLp f))
  exact h.congr fun t => (autocorr_eq_inner_toLp hf t).symm

/-- The origin correlation is the squared L² norm. -/
theorem autocorr_zero_eq_norm_toLp_sq {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    autocorr f 0 = ‖hf.toLp f‖ ^ 2 := by
  rw [autocorr_eq_inner_toLp hf, physicalTranslation_zero, real_inner_self_eq_norm_sq]

/-- Every real L² autocorrelation is bounded in absolute value by its origin value. -/
theorem abs_autocorr_le_zero_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume) (t : ℝ) :
    |autocorr f t| ≤ autocorr f 0 := by
  rw [autocorr_eq_inner_toLp hf t, autocorr_zero_eq_norm_toLp_sq hf, pow_two]
  have h := norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (physicalTranslation t (hf.toLp f))
  simpa only [Real.norm_eq_abs, physicalTranslation_norm] using h

/-- L² approximation controls the correlation error uniformly at every translation. -/
theorem autocorr_sub_le_L2_norms (q r : Velocity) (t : ℝ) :
    |autocorr q t - autocorr r t| ≤ (‖q‖ + ‖r‖) * ‖q-r‖ := by
  rw [autocorr_eq_inner_physicalTranslation, autocorr_eq_inner_physicalTranslation]
  have he : ⟪q, physicalTranslation t q⟫ - ⟪r, physicalTranslation t r⟫ =
      ⟪q-r, physicalTranslation t q⟫ + ⟪r, physicalTranslation t (q-r)⟫ := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |⟪q-r, physicalTranslation t q⟫| + |⟪r, physicalTranslation t (q-r)⟫| := abs_add_le _ _
    _ ≤ ‖q-r‖ * ‖q‖ + ‖r‖ * ‖q-r‖ := add_le_add
      (by simpa only [Real.norm_eq_abs, physicalTranslation_norm] using
        norm_inner_le_norm (𝕜 := ℝ) (q-r) (physicalTranslation t q))
      (by simpa only [Real.norm_eq_abs, physicalTranslation_norm] using
        norm_inner_le_norm (𝕜 := ℝ) r (physicalTranslation t (q-r)))
    _ = _ := by ring

/-- Every real L² source has the exact extended critical primary energy limit.
All profile conditions follow from the source; infinite limiting energy is retained. -/
theorem tendsto_suzukiCriticalCompensatedEnergy_autocorr {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    Tendsto (suzukiCriticalCompensatedEnergy (fun t => autocorr f 0 - autocorr f t))
      (𝓝[>] 0)
      (𝓝 (suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr f 0 - autocorr f t))) := by
  apply tendsto_suzukiCriticalCompensatedEnergy
  · exact measurable_const.sub (continuous_autocorr_of_memLp hf).measurable
  · exact AutocorrelationKrein.deficit_nonneg hf
  · refine ⟨2 * autocorr f 0, fun t => ?_⟩
    have h := (abs_le.mp (abs_autocorr_le_zero_of_memLp hf t)).1
    linarith only [h]

end
end RHTower
