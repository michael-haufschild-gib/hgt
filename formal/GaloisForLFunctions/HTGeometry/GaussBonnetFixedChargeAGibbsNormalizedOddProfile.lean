import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddProfile
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanBarrierError

/-!
# Peak-normalized asymmetric Gibbs profile

The true barrier height has zero linear correction to its quartic scale.
Consequently the first correction to the normalized profile is determined
by the displacement of its peak. Dividing by that actual displacement
removes all charge and coupling dependence from this correction.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMeanGibbsDeficit_fifth_zero_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l / egbCoexistenceASymmetricRatio τ ^ 5)
      atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).mul egbCoexistenceASymmetricRatio_critical_limit
  simp only [mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeAGibbsBarrier_first_correction_limit (w φ l : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsBarrier w φ τ l / egbCoexistenceASymmetricRatio τ ^ 4 -
      egbFixedChargeAGibbsBarrierCoefficient w φ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMeanGibbsGap_first_correction_limit w φ l).add
    (egbFixedChargeAMeanGibbsDeficit_fifth_zero_limit w φ l)
  simp only [add_zero] at h
  convert h using 1
  funext τ
  rw [egbFixedChargeAMeanGibbsDeficit_gap_difference]
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeAGibbsOddCoefficient_barrier_ratio (w φ : ℝ) :
    egbFixedChargeAGibbsOddCoefficient w φ / egbFixedChargeAGibbsBarrierCoefficient w φ =
      4 * egbFixedChargeAMiddleMeanCorrection φ := by
  rw [← egbFixedChargeAGibbsOddCoefficient_peak_displacement w φ]
  ring

theorem egbFixedChargeAInteriorGibbsGap_normalized_first_correction_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      cos ψ ^ 4) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ 4)) := by
  have h := ((egbFixedChargeAInteriorGibbsGap_first_correction_limit w φ l₁ ψ).sub
    ((tendsto_const_nhds (x := cos ψ ^ 4)).mul (egbFixedChargeAGibbsBarrier_first_correction_limit w φ l₂))).div
      (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l₂) (egbFixedChargeAGibbsBarrierCoefficient_pos w φ).ne'
  simp only [mul_zero, sub_zero, Pi.div_def] at h
  have he : egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ 4 / egbFixedChargeAGibbsBarrierCoefficient w φ =
      4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ 4 := by
    rw [← egbFixedChargeAGibbsOddCoefficient_barrier_ratio w φ]
    ring
  rw [he] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hb := egbFixedChargeAGibbsBarrier_pos w φ τ l₂
  field_simp <;> ring

theorem egbFixedChargeAInteriorGibbsGap_peak_displacement_correction_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      cos ψ ^ 4) / egbFixedChargeAMiddleGapCoordinate τ φ)
      atBot (𝓝 (4 * sin ψ * cos ψ ^ 4)) := by
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have h := (egbFixedChargeAInteriorGibbsGap_normalized_first_correction_limit w φ l₁ l₂ ψ).div
    (egbFixedChargeAMiddleGapCoordinate_linear_limit φ) hc.ne
  have he : 4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ 4 / egbFixedChargeAMiddleMeanCorrection φ =
      4 * sin ψ * cos ψ ^ 4 := by field_simp [hc.ne]
  rw [he] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
