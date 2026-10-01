import GaloisForLFunctions.RHTower.ThetaTemperedFourierCorrelation
import GaloisForLFunctions.RHTower.ThetaTemperedTranslationAnnihilator
import GaloisForLFunctions.HTGeometry.SchwartzPositiveMeasureRepresentation

/-!
# Full tempered Fourier kernel of the original theta derivative annihilator

Actual expanding compact cutoffs converge in every original Schwartz seminorm.
Their modulated products recover every modulation probe of an arbitrary tempered
functional. The full Fourier correlation gives the reverse implication. Actual
physical Fourier transport identifies the original all-derivative annihilator
with the whole Xi-multiplier kernel, without a finite-jet or support hypothesis.
-/

open Complex Filter MeasureTheory Topology
open scoped SchwartzMap
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Compact wave tests are genuine members of the original Schwartz space. -/
theorem thetaPhysicalModulatedCutoff_hasCompactSupport (a : ℝ) (n : ℕ) :
    HasCompactSupport (thetaPhysicalModulationCLM a (SchwartzMap.scaledUnitCutoff n)) := by
  have heq :
      (thetaPhysicalModulationCLM a (SchwartzMap.scaledUnitCutoff n) : ℝ → ℂ) =
        modulation a * (SchwartzMap.scaledUnitCutoff n : ℝ → ℂ) := by
    funext t
    exact thetaPhysicalModulationCLM_apply a _ t
  rw [heq]
  exact (SchwartzMap.scaledUnitCutoff_hasCompactSupport n).mul_left

/-- Multiplying a compact wave test by the source is its exact expanding cutoff. -/
theorem thetaSchwartz_cutoffModulation_product_eq (a : ℝ) (n : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ)
        (thetaPhysicalModulationCLM a (SchwartzMap.scaledUnitCutoff n)) =
      SchwartzMap.compactSupportApproximation n (thetaPhysicalModulationCLM a ψ) := by
  ext t
  rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth,
    SchwartzMap.compactSupportApproximation_apply,
    thetaPhysicalModulationCLM_apply, thetaPhysicalModulationCLM_apply, smul_eq_mul]
  ring

/-- Every original weighted seminorm has an explicit inverse-radius error bound. -/
theorem thetaSchwartz_cutoffModulation_product_sub_seminorm_le
    (a : ℝ) (n k m : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    SchwartzMap.seminorm ℂ k m
        (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ)
          (thetaPhysicalModulationCLM a (SchwartzMap.scaledUnitCutoff n)) -
            thetaPhysicalModulationCLM a ψ) ≤
      SchwartzMap.compactSupportApproximationSeminormBound k m
        (thetaPhysicalModulationCLM a ψ) / ((n : ℝ) + 1) := by
  rw [thetaSchwartz_cutoffModulation_product_eq]
  exact SchwartzMap.compactSupportApproximation_sub_seminorm_le n k m _

/-- Compact wave products converge in the installed original Schwartz topology. -/
theorem thetaSchwartz_tendsto_cutoffModulation_product (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun n : ℕ => SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ)
      (thetaPhysicalModulationCLM a (SchwartzMap.scaledUnitCutoff n)))
        atTop (𝓝 (thetaPhysicalModulationCLM a ψ)) := by
  simpa only [thetaSchwartz_cutoffModulation_product_eq] using
    SchwartzMap.tendsto_compactSupportApproximation (thetaPhysicalModulationCLM a ψ)

/-- The full modulation orbit detects the actual multiplier kernel on the entire tempered dual. -/
theorem thetaTempered_modulation_annihilator_iff_multiplier
    (Q : 𝓢'(ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) :
    (∀ a : ℝ, Q (thetaPhysicalModulationCLM a ψ) = 0) ↔
      TemperedDistribution.smulLeftCLM ℂ (ψ : ℝ → ℂ) Q = 0 := by
  constructor
  · intro hQ
    ext φ
    rw [TemperedDistribution.smulLeftCLM_apply_apply,
      thetaTempered_physicalFourier_correlation]
    simp only [hQ, mul_zero, integral_zero]
    rfl
  · intro hQ a
    have hzero : ∀ n : ℕ,
        Q (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ)
          (thetaPhysicalModulationCLM a (SchwartzMap.scaledUnitCutoff n))) = 0 := by
      intro n
      have h := congrArg (fun R : 𝓢'(ℝ, ℂ) =>
        R (thetaPhysicalModulationCLM a (SchwartzMap.scaledUnitCutoff n))) hQ
      simpa only [TemperedDistribution.smulLeftCLM_apply_apply, zero_apply] using h
    have hlim := Q.continuous.continuousAt.tendsto.comp
      (thetaSchwartz_tendsto_cutoffModulation_product a ψ)
    change Tendsto (fun n : ℕ => Q (SchwartzMap.smulLeftCLM ℂ (ψ : ℝ → ℂ)
      (thetaPhysicalModulationCLM a (SchwartzMap.scaledUnitCutoff n))))
        atTop (𝓝 (Q (thetaPhysicalModulationCLM a ψ))) at hlim
    have hconst : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop
        (𝓝 (Q (thetaPhysicalModulationCLM a ψ))) := by
      simpa only [hzero] using hlim
    exact (tendsto_const_nhds_iff.mp hconst).symm

/-- The exact physical transform of the original installed real translation. -/
theorem thetaPhysicalFourierCLE_schwartzTranslate (a : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    thetaPhysicalFourierCLE (MellinL2.schwartzTranslate a φ) =
      thetaPhysicalModulationCLM a (thetaPhysicalFourierCLE φ) := by
  have htranslate : MellinL2.schwartzTranslate a φ = SchwartzMap.translateCLM ℂ a φ := by
    ext t
    rw [MellinL2.schwartzTranslate_apply, SchwartzMap.translateCLM_apply]
  rw [htranslate]
  ext t
  rw [thetaPhysicalFourierCLE_translateCLM_apply, thetaPhysicalModulationCLM_apply]

/-- Every spectral tempered functional belongs to the actual Xi kernel exactly when its
physical Fourier pullback annihilates every original theta source derivative. -/
theorem thetaPhysicalTemperedPullback_mem_annihilator_iff_Xi_kernel (Q : 𝓢'(ℝ, ℂ)) :
    thetaPhysicalTemperedPullback Q ∈ thetaUnscaledTemperedDerivativeAnnihilator ↔
      thetaXiTemperedMultiplier Q = 0 := by
  rw [thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_schwartzTranslates]
  simp only [thetaPhysicalTemperedPullback_apply, thetaPhysicalFourierCLE_schwartzTranslate]
  rw [thetaTempered_modulation_annihilator_iff_multiplier, thetaPhysicalFourierCLE_source]
  rfl

/-- The full all-test Fourier-kernel criterion for an arbitrary original tempered functional. -/
theorem thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_Xi_inverseFourier_kernel
    (T : 𝓢'(ℝ, ℂ)) :
    T ∈ thetaUnscaledTemperedDerivativeAnnihilator ↔
      thetaXiTemperedMultiplier (thetaPhysicalTemperedInversePullback T) = 0 := by
  simpa only [thetaPhysicalTemperedPullback_inversePullback] using
    thetaPhysicalTemperedPullback_mem_annihilator_iff_Xi_kernel
      (thetaPhysicalTemperedInversePullback T)

/-- The original annihilator is the exact inverse-Fourier preimage of the entire Xi kernel. -/
theorem thetaUnscaledTemperedDerivativeAnnihilator_eq_Xi_kernel_comap :
    thetaUnscaledTemperedDerivativeAnnihilator =
      (LinearMap.ker thetaXiTemperedMultiplier.toLinearMap).comap
        thetaPhysicalTemperedInversePullback.toLinearMap := by
  apply Submodule.ext
  intro T
  simpa only [Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] using
    thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_Xi_inverseFourier_kernel T

/-- Original (8): the complete Xi kernel maps onto the whole theta derivative annihilator. -/
theorem thetaUnscaledTemperedDerivativeAnnihilator_eq_Xi_kernel_map :
    thetaUnscaledTemperedDerivativeAnnihilator =
      (LinearMap.ker thetaXiTemperedMultiplier.toLinearMap).map
        thetaPhysicalTemperedPullback.toLinearMap := by
  apply Submodule.ext
  intro T
  rw [Submodule.mem_map]
  constructor
  · intro hT
    refine ⟨thetaPhysicalTemperedInversePullback T, ?_,
      thetaPhysicalTemperedPullback_inversePullback T⟩
    exact LinearMap.mem_ker.mpr
      ((thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_Xi_inverseFourier_kernel T).mp hT)
  · rintro ⟨Q, hQ, rfl⟩
    exact (thetaPhysicalTemperedPullback_mem_annihilator_iff_Xi_kernel Q).mpr
      (LinearMap.mem_ker.mp hQ)

end RHTower
