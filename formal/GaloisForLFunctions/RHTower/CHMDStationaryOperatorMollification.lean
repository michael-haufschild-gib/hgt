import GaloisForLFunctions.RHTower.CHMDStationaryTranslations

/-!
# Mollification in the stationary operator graph

The Bochner average of translations commutes with the actual stationary
resolvent. It therefore preserves the unbounded generator's domain and
converges simultaneously in the source and generator coordinates.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace Convolution
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar WeilOneSided

def volumeSmooth (n : ℕ) (u : StationaryVolumeSpace) : StationaryVolumeSpace :=
  ∫ a : ℝ, mollifier n a • volumeTranslate (-a) u

theorem integrable_volumeSmooth (n : ℕ) (u : StationaryVolumeSpace) :
    Integrable (fun a : ℝ => mollifier n a • volumeTranslate (-a) u) := by
  have hc : Continuous (fun a : ℝ => mollifier n a • volumeTranslate (-a) u) :=
    (mollifier_contDiff n).continuous.smul ((continuous_volumeTranslate u).comp continuous_neg)
  exact hc.integrable_of_hasCompactSupport (mollifier_compact n).smul_right

theorem volumeSmooth_sub (n : ℕ) (u v : StationaryVolumeSpace) :
    volumeSmooth n (u - v) = volumeSmooth n u - volumeSmooth n v := by
  simp only [volumeSmooth, map_sub, smul_sub]
  exact integral_sub (integrable_volumeSmooth n u) (integrable_volumeSmooth n v)

theorem volumeSmooth_tendsto (u : StationaryVolumeSpace) :
    Tendsto (fun n => volumeSmooth n u) atTop (𝓝 u) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℝ))
    narrowBump_rOut_tendsto (continuous_volumeTranslate u) 0
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    volumeTranslate_zero, volumeSmooth, mollifier] using h

theorem volumeResolvent_smooth (n : ℕ) (w : StationaryVolumeSpace) :
    volumeResolvent (volumeSmooth n w) = volumeSmooth n (volumeResolvent w) := by
  rw [volumeSmooth, ← volumeResolvent.integral_comp_comm (integrable_volumeSmooth n w)]
  apply integral_congr_ae
  exact Eventually.of_forall fun a => by rw [map_smul, volumeResolvent_translate]

def volumeGeneratorSmooth (n : ℕ) (u : volumeGenerator.domain) : volumeGenerator.domain :=
  ⟨volumeSmooth n (u : StationaryVolumeSpace),
    ⟨volumeSmooth n ((u : StationaryVolumeSpace) + volumeGenerator u), by
      rw [volumeResolvent_smooth,
        generatorOfResolvent_identity volumeResolvent volumeResolvent_injective u]⟩⟩

theorem volumeGeneratorSmooth_apply (n : ℕ) (u : volumeGenerator.domain) :
    volumeGenerator (volumeGeneratorSmooth n u) = volumeSmooth n (volumeGenerator u) := by
  rcases u with ⟨u, hu⟩
  obtain ⟨w, rfl⟩ := hu
  have he : volumeGeneratorSmooth n ⟨volumeResolvent w, ⟨w, rfl⟩⟩ =
      ⟨volumeResolvent (volumeSmooth n w), ⟨volumeSmooth n w, rfl⟩⟩ := by
    apply Subtype.ext
    exact (volumeResolvent_smooth n w).symm
  rw [he, volumeGenerator_resolvent, volumeGenerator_resolvent, volumeSmooth_sub,
    volumeResolvent_smooth]

theorem volumeGeneratorSmooth_tendsto (u : volumeGenerator.domain) :
    Tendsto (fun n => (volumeGeneratorSmooth n u : StationaryVolumeSpace)) atTop
      (𝓝 (u : StationaryVolumeSpace)) ∧
    Tendsto (fun n => volumeGenerator (volumeGeneratorSmooth n u)) atTop
      (𝓝 (volumeGenerator u)) := by
  constructor
  · exact volumeSmooth_tendsto _
  · simpa only [volumeGeneratorSmooth_apply] using volumeSmooth_tendsto (volumeGenerator u)

end RHTower.CHMDDoobGraph
