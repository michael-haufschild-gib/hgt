import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsUniformNormalization
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakAlignedUniformCorrection

/-!
# Gibbs asymptotics along arbitrary moving interior radii

Uniformity removes the need for a fixed radius coordinate. Every real
angle trajectory is allowed, without continuity, convergence, or
smallness hypotheses. The peak-aligned energy residual is uniformly
little-o of the phase asymmetry and remains negligible along every
such moving trajectory.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsOddKernel_moving_residual_limit (w φ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsOddKernel w φ τ (sin (ψ τ)) -
      egbFixedChargeAGibbsOddLimitKernel w φ (sin (ψ τ))) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformlyOn_iff.mp (egbFixedChargeAGibbsOddKernel_uniform_critical_limit w φ)) ε hε
  filter_upwards [h] with τ hτ
  have he := hτ (sin (ψ τ)) ⟨neg_one_le_sin (ψ τ), sin_le_one (ψ τ)⟩
  simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using he

theorem egbFixedChargeAInteriorGibbsGap_moving_fifth_residual_limit (w φ l : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l (ψ τ) -
      egbFixedChargeAGibbsBarrierCoefficient w φ * cos (ψ τ) ^ 4 * egbCoexistenceASymmetricRatio τ ^ 4) /
      egbCoexistenceASymmetricRatio τ ^ 5 - egbFixedChargeAGibbsOddCoefficient w φ * sin (ψ τ) * cos (ψ τ) ^ 4)
      atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAInteriorGibbsGap_uniform_fifth_order_limit w φ l)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hτ (ψ τ)

theorem egbFixedChargeAInteriorGibbsGap_moving_normalized_residual_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ (ψ τ) / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      cos (ψ τ) ^ 4) / egbCoexistenceASymmetricRatio τ -
      4 * egbFixedChargeAMiddleMeanCorrection φ * sin (ψ τ) * cos (ψ τ) ^ 4) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAInteriorGibbsGap_uniform_normalized_first_limit w φ l₁ l₂)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hτ (ψ τ)

theorem egbFixedChargeAInteriorGibbsGap_uniform_aligned_first_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      egbFixedChargeAPeakAlignedProfile τ φ ψ) / egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  have h := (egbFixedChargeAInteriorGibbsGap_uniform_normalized_first_limit w φ l₁ l₂).sub
    (egbFixedChargeAPeakAlignedProfile_uniform_first_limit φ)
  simp only [sub_self] at h
  change TendstoUniformly (fun τ ψ =>
    (egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ - cos ψ ^ 4) /
      egbCoexistenceASymmetricRatio τ -
    (egbFixedChargeAPeakAlignedProfile τ φ ψ - cos ψ ^ 4) / egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot at h
  convert h using 1
  funext τ ψ
  ring

theorem egbFixedChargeAInteriorGibbsGap_moving_aligned_first_zero_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ (ψ τ) / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      egbFixedChargeAPeakAlignedProfile τ φ (ψ τ)) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAInteriorGibbsGap_uniform_aligned_first_zero_limit w φ l₁ l₂)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [dist_comm] using hτ (ψ τ)

theorem egbFixedChargeAInteriorGibbsGap_moving_aligned_peak_zero_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ (ψ τ) / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      egbFixedChargeAPeakAlignedProfile τ φ (ψ τ)) / egbFixedChargeAMiddleGapCoordinate τ φ) atBot (𝓝 (0 : ℝ)) := by
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have h := (egbFixedChargeAInteriorGibbsGap_moving_aligned_first_zero_limit w φ l₁ l₂ ψ).div
    (egbFixedChargeAMiddleGapCoordinate_linear_limit φ) hc.ne
  simp only [zero_div, Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
