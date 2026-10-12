import GaloisForLFunctions.HTGeometry.MomentConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-! A uniform second moment upgrades weak convergence to convergence of the
expectation of a continuous, potentially unbounded observable. -/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem tendsto_integral_continuous_of_uniform_square_bound
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hweak : Tendsto μs atTop (𝓝 μ)) {f : Ω → ℝ} (hf : Continuous f)
    (hs : ∀ r, Integrable (fun x => f x ^ 2) (μs r : Measure Ω))
    (hμ : Integrable (fun x => f x ^ 2) (μ : Measure Ω))
    {C : ℝ} (hC : ∀ᶠ r in atTop, (∫ x, f x ^ 2 ∂(μs r : Measure Ω)) ≤ C) :
    Tendsto (fun r => ∫ x, f x ∂(μs r : Measure Ω)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  let νs := fun r => (μs r).map hf.measurable.aemeasurable
  let ν := μ.map hf.measurable.aemeasurable
  have hmap : Tendsto νs atTop (𝓝 ν) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hweak hf
  have hI (σ : ProbabilityMeasure Ω) (p : ℕ) :
      (∫ y : ℝ, y ^ p ∂(σ.map hf.measurable.aemeasurable : Measure ℝ)) =
        ∫ x, f x ^ p ∂(σ : Measure Ω) := by
    exact integral_map hf.measurable.aemeasurable
      (continuous_id.pow p).aestronglyMeasurable
  have hi (σ : ProbabilityMeasure Ω) (p : ℕ) :
      Integrable (fun y : ℝ => y ^ p) (σ.map hf.measurable.aemeasurable : Measure ℝ) ↔
        Integrable (fun x => f x ^ p) (σ : Measure Ω) :=
    integrable_map_measure (continuous_id.pow p).aestronglyMeasurable hf.measurable.aemeasurable
  have hfirst (σ : ProbabilityMeasure Ω)
      (hσ : Integrable (fun x => f x ^ 2) (σ : Measure Ω)) :
      Integrable f (σ : Measure Ω) :=
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hσ).integrable (by norm_num)
  have h := _root_.HTGeometry.tendsto_integral_pow_of_uniform_even_moment (k := 1)
    (by norm_num) (μ := (ν : Measure ℝ)) (νs := fun r => (νs r : Measure ℝ))
    (M := max C (∫ x, f x ^ 2 ∂(μ : Measure Ω)))
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmap)
    (hC.mono fun r hr => by simpa only [νs, hI, mul_one] using hr.trans (le_max_left _ _))
    (by simpa only [ν, hI, mul_one] using le_max_right C (∫ x, f x ^ 2 ∂(μ : Measure Ω)))
    (fun r => (hi (μs r) 1).mpr (by simpa only [pow_one] using hfirst (μs r) (hs r)))
    (fun r => by simpa only [νs, mul_one] using (hi (μs r) 2).mpr (hs r))
    (fun R hR r => (_root_.HTGeometry.truncPowBCF R hR.le 1).integrable (νs r : Measure ℝ))
    ((hi μ 1).mpr (by simpa only [pow_one] using hfirst μ hμ))
    (by simpa only [ν, mul_one] using (hi μ 2).mpr hμ)
    (fun R hR => (_root_.HTGeometry.truncPowBCF R hR.le 1).integrable (ν : Measure ℝ))
  dsimp only [νs, ν] at h
  simp_rw [hI] at h
  simpa only [pow_one] using h

end GaloisForLFunctions.HTGeometry
