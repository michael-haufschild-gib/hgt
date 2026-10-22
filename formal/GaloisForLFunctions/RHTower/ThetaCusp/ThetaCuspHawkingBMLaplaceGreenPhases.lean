import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceGreenBoundary

/-! Actual endpoint Wronskian phases of the full retained-source inverse. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def ingoingPhase (w chi s a J K T : ℂ) (z : ℝ) : ℂ :=
  integratingFactor z*(horizon w chi z*responseFirst w chi s a J K T z-
    horizonFirst w chi z*response w chi s a J K T z)

def outerPhase (w chi s a J K T : ℂ) (z : ℝ) : ℂ :=
  integratingFactor z*(response w chi s a J K T z*normalizableFirst w chi z-
    responseFirst w chi s a J K T z*normalizable w chi z)

/-- The original response's actual Wronskian phases equal the full endpoint
source moments with their proved physical normalization. -/
theorem response_phase_moments {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    {z : ℝ} (hz : z ∈ Ioo 0 1) :
    ingoingPhase w chi s a J K T z=(-connection w chi/2)*horizonMoment w chi s a J K T z ∧
    outerPhase w chi s a J K T z=(-connection w chi/2)*outerMoment w chi s a J K T z := by
  have hW := wronskian_eq h hz
  dsimp [wronskian] at hW
  constructor
  · dsimp [ingoingPhase,response,responseFirst]
    linear_combination (horizonMoment w chi s a J K T z)*hW
  · dsimp [outerPhase,response,responseFirst]
    linear_combination (outerMoment w chi s a J K T z)*hW

/-- Both true endpoint boundary phases vanish, as consequences of source
admission and the actual Green response. -/
theorem response_endpoint_phases {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    Tendsto (ingoingPhase w chi s a J K T) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (outerPhase w chi s a J K T) (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have hc := greenMoments_continuousOn h s a J K T
  constructor
  · have hA := (hc.1 0 (by norm_num)).mono Ioo_subset_Icc_self
    rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsGT (show (0:ℝ)<1 by norm_num)] at hA
    have hA0 : horizonMoment w chi s a J K T 0=0 := by simp [horizonMoment]
    rw [hA0] at hA
    have ht := hA.const_mul (-connection w chi/2)
    simp only [mul_zero] at ht
    apply ht.congr'
    have hlt : ∀ᶠ z : ℝ in 𝓝[>] (0:ℝ), z < 1 :=
      (show ∀ᶠ z : ℝ in 𝓝 0, z < 1 from Iio_mem_nhds (by norm_num)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,hlt] with z hz0 hz1
    exact (response_phase_moments h s a J K T ⟨hz0,hz1⟩).1.symm
  · have hB := (hc.2 1 (by norm_num)).mono Ioo_subset_Icc_self
    rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsLT (show (0:ℝ)<1 by norm_num)] at hB
    have hB0 : outerMoment w chi s a J K T 1=0 := by simp [outerMoment]
    rw [hB0] at hB
    have ht := hB.const_mul (-connection w chi/2)
    simp only [mul_zero] at ht
    apply ht.congr'
    have hgt : ∀ᶠ z : ℝ in 𝓝[<] (1:ℝ), 0 < z :=
      (show ∀ᶠ z : ℝ in 𝓝 1, 0 < z from Ioi_mem_nhds (by norm_num)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,hgt] with z hz1 hz0
    exact (response_phase_moments h s a J K T ⟨hz0,hz1⟩).2.symm

end
end RHTower.D4BMLaplaceRadial
