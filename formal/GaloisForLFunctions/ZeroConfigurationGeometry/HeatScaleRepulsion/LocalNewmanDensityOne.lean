import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightLocalNewman
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.DensityOneExtraction

/-!
# Vanishing normalized local Newman constant on a density-one set

The exceptional set at every positive normalized level has density zero.
A diagonal truncation gives one measurable density-one set on which the
normalized constant converges to zero. On this same set, every fixed
positive inverse-logarithmic heat scale eventually lies beyond all
nonreal zeros in the unit window, uniformly over later heat times.
-/

open Complex Filter Topology Set MeasureTheory
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The actual local de Bruijn–Newman constant has vanishing normalized value on a measurable density-one set. -/
theorem exists_densityOne_localNewman_scaled_tendsto_zero :
    ∃ S : Set ℝ, MeasurableSet S ∧
      (∀ δ > 0, ∀ᶠ H : ℝ in atTop,
        volume (Sᶜ ∩ Icc 0 H) ≤ ENNReal.ofReal (δ * H)) ∧
      Tendsto (fun X : ℝ => localNewmanConstant X * Real.log X)
        (atTop ⊓ 𝓟 S) (𝓝 0) := by
  apply exists_measurable_densityOne_tendsto_zero_of_density_zero
  · intro X hX
    exact mul_nonneg (localNewmanConstant_nonneg X) (Real.log_nonneg hX)
  · intro ε hε δ hδ
    exact eventually_volume_localNewman_scaled_gt_inter_Icc_le hε hδ

/-- On one density-one set, every positive inverse-logarithmic heat scale eventually gives reality for all future times. -/
theorem exists_densityOne_eventual_local_heat_reality :
    ∃ S : Set ℝ, MeasurableSet S ∧
      (∀ δ > 0, ∀ᶠ H : ℝ in atTop,
        volume (Sᶜ ∩ Icc 0 H) ≤ ENNReal.ofReal (δ * H)) ∧
      Tendsto (fun X : ℝ => localNewmanConstant X * Real.log X) (atTop ⊓ 𝓟 S) (𝓝 0) ∧
      ∀ κ > 0, ∀ᶠ X : ℝ in atTop ⊓ 𝓟 S,
        ∀ τ : ℝ, κ / Real.log X ≤ τ → ∀ z : ℂ,
          riemannHeat τ z = 0 → |z.re - X| ≤ 1 → z.im = 0 := by
  obtain ⟨S, hSm, hD, hlim⟩ := exists_densityOne_localNewman_scaled_tendsto_zero
  refine ⟨S, hSm, hD, hlim, ?_⟩
  intro κ hκ
  have hsmall := hlim.eventually (eventually_lt_nhds hκ)
  have hlarge : ∀ᶠ X : ℝ in atTop ⊓ 𝓟 S, 1 < X :=
    (eventually_gt_atTop (1 : ℝ)).filter_mono inf_le_left
  filter_upwards [hsmall, hlarge] with X hsmall hX
  intro τ hτ z hz hre
  by_contra him
  have hτΛ := le_localNewmanConstant_of_nonreal hz him hre
  have hlog := Real.log_pos hX
  have hstart := (div_le_iff₀ hlog).mp hτ
  have hh := mul_le_mul_of_nonneg_right hτΛ hlog.le
  linarith only [hsmall, hstart, hh]

#print axioms exists_densityOne_localNewman_scaled_tendsto_zero
#print axioms exists_densityOne_eventual_local_heat_reality

end

end GaloisForLFunctions.ZeroConfigurationGeometry
