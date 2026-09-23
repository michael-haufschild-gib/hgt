import GaloisForLFunctions.RHTower.XiGaussianExplicitFormulaRectangle
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalBound

/-!
# Complex-time Xi heat source contours and the RH vertical bound

Under RH, the centered complex Gaussian is absolutely summable on the Xi divisor throughout the
open right heat half-plane. General rectangle synthesis therefore realizes the complex-time heat
trace as a limit of continued prime--archimedean source contours, whose norms inherit the RH
vertical cancellation bound up to arbitrary accuracy.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The centered Gaussian test at complex heat time. -/
def xiGaussianComplexTestC (τ z : ℂ) : ℂ :=
  Complex.exp (-τ * z ^ (2 : ℕ))

theorem differentiable_xiGaussianComplexTestC (τ : ℂ) :
    Differentiable ℂ (xiGaussianComplexTestC τ) := by
  unfold xiGaussianComplexTestC
  fun_prop

theorem analyticOnNhd_xiGaussianComplexTestC (τ : ℂ) :
    AnalyticOnNhd ℂ (xiGaussianComplexTestC τ) Set.univ := fun z _ =>
  ((differentiable_xiGaussianComplexTestC τ).differentiableOn
    (s := Set.univ)).analyticOnNhd isOpen_univ z (Set.mem_univ z)

/-- The complex Gaussian test evaluated on the centered divisor is exactly the complex heat
multiplier. -/
theorem xiGaussianComplexTestC_spectralPoint (τ : ℂ) (q : XiZeroCopy) :
    xiGaussianComplexTestC τ (xiSpectralPoint q) =
      xiGaussianHeatTermC τ q :=
  rfl

/-- Under RH, normalized arithmetic source contours approximate the complete complex-time heat
trace at every time in the open right heat half-plane. -/
theorem exists_admissible_complexGaussianSource_contour_approximates_heatTraceC_of_rh
    (hRH : RiemannHypothesis) {τ : ℂ} (hτ : 0 < τ.re)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      dist ((2 * Real.pi * I)⁻¹ *
          rectIntegral (fun z => xiGaussianComplexTestC τ z *
            continuedPrimeArchSourceRelativeTrace z) z₁ z₂)
        (xiGaussianHeatTraceC τ) < epsilon := by
  classical
  set f : XiZeroCopy → ℂ := fun q => xiGaussianHeatTermC τ q with hf
  have hsum : Summable f :=
    summable_norm_iff.mp (summable_norm_xiGaussianHeatTermC_of_rh hRH hτ)
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨F, hF⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hcontains, hcontour⟩ :=
    exists_admissible_rectIntegral_source_eq_xiZeroCopy_sum_containing F
      (analyticOnNhd_xiGaussianComplexTestC τ)
  refine ⟨z₁, z₂, hre, him, ?_⟩
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have hpi0 : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    simp [hpi0, Complex.I_ne_zero]
  have hnorm : (2 * Real.pi * I : ℂ)⁻¹ *
      rectIntegral (fun z => xiGaussianComplexTestC τ z *
        continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, f q := by
    rw [hcontour, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
    exact Finset.sum_congr rfl fun q _ =>
      xiGaussianComplexTestC_spectralPoint τ q
  rw [hnorm, xiGaussianHeatTraceC]
  have hsubset : F ⊆ xiZeroCopyClosedRectangle z₁ z₂ := fun q hq => hcontains q hq
  exact hF _ hsubset

/-- **Xi complex-heat source-contour vertical-bound universality.** Under RH, every complex heat
trace in the open right half-plane has arbitrarily accurate arithmetic source-contour
approximants, and every such chosen approximant can be made to obey the RH vertical norm bound up
to the same prescribed error. -/
theorem xi_complexHeat_sourceContourVerticalBoundUniversality
    (hRH : RiemannHypothesis) {τ : ℂ} (hτ : 0 < τ.re)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      let C := (2 * Real.pi * I)⁻¹ *
        rectIntegral (fun z => xiGaussianComplexTestC τ z *
          continuedPrimeArchSourceRelativeTrace z) z₁ z₂
      dist C (xiGaussianHeatTraceC τ) < epsilon ∧
        ‖C‖ < xiGaussianHeatTraceReal τ.re + epsilon := by
  obtain ⟨z₁, z₂, hre, him, hdist⟩ :=
    exists_admissible_complexGaussianSource_contour_approximates_heatTraceC_of_rh
      hRH hτ hepsilon
  refine ⟨z₁, z₂, hre, him, hdist, ?_⟩
  let C := (2 * Real.pi * I)⁻¹ *
    rectIntegral (fun z => xiGaussianComplexTestC τ z *
      continuedPrimeArchSourceRelativeTrace z) z₁ z₂
  have htriangle : ‖C‖ ≤ ‖xiGaussianHeatTraceC τ‖ +
      dist C (xiGaussianHeatTraceC τ) := by
    rw [dist_eq]
    calc
      ‖C‖ = ‖xiGaussianHeatTraceC τ + (C - xiGaussianHeatTraceC τ)‖ := by
        congr 1
        ring
      _ ≤ ‖xiGaussianHeatTraceC τ‖ + ‖C - xiGaussianHeatTraceC τ‖ := norm_add_le _ _
  have hvertical := norm_xiGaussianHeatTraceC_le_of_rh hRH hτ
  dsimp only [C] at htriangle
  linarith

end

end RHTower
