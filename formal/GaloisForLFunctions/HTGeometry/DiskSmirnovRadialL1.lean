import GaloisForLFunctions.HTGeometry.DiskSmirnovAnalyticValue
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryInnerOuterFactor

/-!
# Radial `L¹` admission for Smirnov boundary quotients

A uniform circle `L¹` bound on all Abel radial values passes to the exact boundary quotient.
This is the reusable Fatou step behind endpoint `N⁺` constructions.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem continuous_norm_radialBoundaryFun
    (F : DiskSmirnovBoundary) (n : ℕ) :
    Continuous fun z : Circle => ‖F.radialBoundaryFun n z‖ := by
  have harg : ∀ z : Circle,
      (hardyDiskAbelRadius n : ℂ) * (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    intro z
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hardyDiskAbelRadius_nonneg n), Circle.norm_coe, mul_one]
    exact hardyDiskAbelRadius_lt_one n
  have hcontinuous : Continuous fun z : Circle =>
      F.value ((hardyDiskAbelRadius n : ℂ) * (z : ℂ)) :=
    F.analyticOnNhd_value.continuousOn.comp_continuous
      (continuous_const.mul continuous_subtype_val) harg
  simpa [DiskSmirnovBoundary.radialBoundaryFun,
    DiskSmirnovBoundary.value, diskMultiplierRadialBoundaryFun] using
      hcontinuous.norm

/-- A uniform `L¹` bound on the Abel radial values of a Smirnov quotient passes to its exact
circle boundary. -/
theorem DiskSmirnovBoundary.integrable_circleBoundary_of_uniform_radial_norm
    (F : DiskSmirnovBoundary) (C : ℝ)
    (hbound : ∀ n : ℕ,
      (∫ z : Circle, ‖F.radialBoundaryFun n z‖ ∂circleLebesgue) ≤ C) :
    Integrable F.circleBoundary circleLebesgue := by
  obtain ⟨ns, hns, hconv⟩ := F.exists_radialBoundary_subseq_ae
  let g : ℕ → Circle → ℝ≥0∞ := fun i z =>
    ENNReal.ofReal ‖F.radialBoundaryFun (ns i) z‖
  have hgMeas : ∀ i, Measurable (g i) := by
    intro i
    exact (ENNReal.continuous_ofReal.comp
      (continuous_norm_radialBoundaryFun F (ns i))).measurable
  have hgBound : ∀ i,
      (∫⁻ z : Circle, g i z ∂circleLebesgue) ≤ ENNReal.ofReal C := by
    intro i
    have hi : Integrable (fun z : Circle => ‖F.radialBoundaryFun (ns i) z‖)
        circleLebesgue := by
      simpa [MeasureTheory.IntegrableOn] using
        (continuous_norm_radialBoundaryFun F (ns i)).continuousOn.integrableOn_compact
          (K := Set.univ) (μ := circleLebesgue) isCompact_univ
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound (ns i))
  have hfatou := lintegral_liminf_le (μ := circleLebesgue) hgMeas
      (u := atTop)
  have hliminfBound :
      liminf (fun i => ∫⁻ z : Circle, g i z ∂circleLebesgue) atTop ≤
        ENNReal.ofReal C :=
    liminf_le_of_frequently_le (Eventually.of_forall hgBound).frequently
  have hpoint : ∀ᵐ z ∂circleLebesgue,
      liminf (fun i => g i z) atTop =
        ENNReal.ofReal ‖F.circleBoundary z‖ := by
    filter_upwards [hconv] with z hz
    have ht : Tendsto (fun i => ‖F.radialBoundaryFun (ns i) z‖) atTop
        (nhds ‖F.circleBoundary z‖) := hz.norm
    exact (ENNReal.tendsto_ofReal ht).liminf_eq
  have hfinite :
      (∫⁻ z : Circle, ENNReal.ofReal ‖F.circleBoundary z‖
        ∂circleLebesgue) < ∞ := by
    calc
      (∫⁻ z : Circle, ENNReal.ofReal ‖F.circleBoundary z‖
          ∂circleLebesgue) =
          ∫⁻ z : Circle, liminf (fun i => g i z) atTop
            ∂circleLebesgue := by
        apply lintegral_congr_ae
        filter_upwards [hpoint] with z hz
        exact hz.symm
      _ ≤ liminf (fun i => ∫⁻ z : Circle, g i z ∂circleLebesgue) atTop := hfatou
      _ ≤ ENNReal.ofReal C := hliminfBound
      _ < ∞ := ENNReal.ofReal_lt_top
  have hnum := diskMultiplierBoundaryMeasurableRep_ae F.numerator
  have hden := diskMultiplierBoundaryMeasurableRep_ae F.denominator
  have hrep : F.circleBoundary =ᵐ[circleLebesgue]
      F.circleBoundaryMeasurableRep := by
    filter_upwards [hnum, hden] with z hzNum hzDen
    simp only [DiskSmirnovBoundary.circleBoundary,
      DiskSmirnovBoundary.circleBoundaryMeasurableRep, hzNum, hzDen]
  refine ⟨F.measurable_circleBoundaryMeasurableRep.aestronglyMeasurable.congr
      hrep.symm, ?_⟩
  simpa only [MeasureTheory.HasFiniteIntegral, ofReal_norm] using hfinite

end

end GaloisForLFunctions.HTGeometry
