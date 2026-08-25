import GaloisForLFunctions.HTGeometry.CayleyBoundaryL2
import GaloisForLFunctions.HTGeometry.DiskMultiplierPrivalov

open MeasureTheory Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Measurable real-line boundary representative of a bounded disk multiplier, obtained by the
exact boundary Cayley transform. -/
def diskMultiplierLineBoundary (φ : DiskMultiplier) (x : ℝ) : ℂ :=
  diskMultiplierBoundaryMeasurableRep φ (circleCayley x)

theorem measurable_diskMultiplierLineBoundary (φ : DiskMultiplier) :
    Measurable (diskMultiplierLineBoundary φ) :=
  (measurable_diskMultiplierBoundaryMeasurableRep φ).comp
    continuous_circleCayley.measurable

/-- The measurable line representative agrees almost everywhere with the literal
Riesz--Fischer boundary pulled back by Cayley. -/
theorem diskMultiplierLineBoundary_ae (φ : DiskMultiplier) :
    diskMultiplierLineBoundary φ =ᵐ[volume]
      fun x => diskMultiplierBoundaryFun φ (circleCayley x) := by
  have hweighted := (diskMultiplierBoundaryMeasurableRep_ae φ).comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  exact (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweighted

/-- Every nonzero bounded analytic multiplier has nonzero real-line boundary almost everywhere. -/
theorem diskMultiplierLineBoundary_ne_zero_ae
    (φ : DiskMultiplier)
    (hφ : ∃ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    ∀ᵐ x ∂volume, diskMultiplierLineBoundary φ x ≠ 0 := by
  have hweighted :=
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae.eventually
      (diskMultiplierBoundary_ne_zero_ae φ hφ)
  have hweightedEq :
      (fun x => diskMultiplierBoundaryFun φ (circleCayley x) ≠ 0) =ᵐ[
        (volume : Measure ℝ).withDensity (realDensity standardCauchyWeight)]
          fun _ => True := by
    filter_upwards [hweighted] with x hx
    simp [hx]
  have hvolumeEq := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweightedEq
  have hvolume : ∀ᵐ x ∂volume,
      diskMultiplierBoundaryFun φ (circleCayley x) ≠ 0 := by
    filter_upwards [hvolumeEq] with x hx
    simpa using hx
  filter_upwards [hvolume, diskMultiplierLineBoundary_ae φ] with x hx hrep
  rwa [hrep]

/-- Analytic sup bound for the real-line boundary representative. -/
theorem ae_norm_diskMultiplierLineBoundary_le (φ : DiskMultiplier) :
    ∀ᵐ x ∂volume, ‖diskMultiplierLineBoundary φ x‖ ≤ φ.bd := by
  have hweighted :=
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae.eventually
      (ae_norm_diskMultiplierBoundaryFun_le φ)
  have hweightedEq :
      (fun x => ‖diskMultiplierBoundaryFun φ (circleCayley x)‖ ≤ φ.bd) =ᵐ[
        (volume : Measure ℝ).withDensity (realDensity standardCauchyWeight)]
          fun _ => True := by
    filter_upwards [hweighted] with x hx
    simp [hx]
  have hvolumeEq := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweightedEq
  have hvolume : ∀ᵐ x ∂volume,
      ‖diskMultiplierBoundaryFun φ (circleCayley x)‖ ≤ φ.bd := by
    filter_upwards [hvolumeEq] with x hx
    simpa using hx
  filter_upwards [hvolume, diskMultiplierLineBoundary_ae φ] with x hx hrep
  rwa [hrep]

/-- Exact multiplication law for bounded analytic line-boundary representatives. -/
theorem diskMultiplierLineBoundary_mul_ae (φ ψ : DiskMultiplier) :
    diskMultiplierLineBoundary (φ.mul ψ) =ᵐ[volume]
      fun x => diskMultiplierLineBoundary φ x * diskMultiplierLineBoundary ψ x := by
  have hweighted := (diskMultiplierBoundaryFun_mul_ae φ ψ).comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hvolume := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweighted
  filter_upwards [hvolume, diskMultiplierLineBoundary_ae (φ.mul ψ),
    diskMultiplierLineBoundary_ae φ, diskMultiplierLineBoundary_ae ψ]
      with x hmul hprod hφ hψ
  have hmul' : diskMultiplierBoundaryFun (φ.mul ψ) (circleCayley x) =
      diskMultiplierBoundaryFun φ (circleCayley x) *
        diskMultiplierBoundaryFun ψ (circleCayley x) := by
    simpa [Function.comp_apply] using hmul
  rw [hprod, hmul', hφ, hψ]

end

end GaloisForLFunctions.HTGeometry
