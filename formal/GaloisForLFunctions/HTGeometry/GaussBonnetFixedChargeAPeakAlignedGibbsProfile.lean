import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakAlignedRadius
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsMovingProfiles

/-!
# Uniform physical Gibbs profile in moving-peak coordinates

The actual barrier-normalized energy tends uniformly to the fixed
quartic profile in coordinates centered on the actual moving peak.
Its residual divided by phase asymmetry tends uniformly to zero.
These estimates remain true along arbitrary moving aligned coordinates.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakAlignedGibbsGap (w φ τ l ψ : ℝ) : ℝ :=
  egbFixedChargeAInteriorGibbsGap w φ τ l (egbFixedChargeAPeakInverseAngle τ φ ψ)

theorem egbFixedChargeAPeakAlignedGibbsGap_formula (w φ τ l ψ : ℝ) :
    egbFixedChargeAPeakAlignedGibbsGap w φ τ l ψ =
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAPeakAlignedRadius w φ τ ψ) -
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) := rfl

theorem egbFixedChargeAPeakAlignedGibbsGap_reference_independent (w φ τ l₁ l₂ ψ : ℝ) :
    egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ ψ = egbFixedChargeAPeakAlignedGibbsGap w φ τ l₂ ψ :=
  egbFixedChargeAInteriorGibbsGap_reference_independent w φ τ l₁ l₂ (egbFixedChargeAPeakInverseAngle τ φ ψ)

theorem egbFixedChargeAPeakAlignedGibbsGap_bounds (w φ τ l ψ : ℝ) :
    0 ≤ egbFixedChargeAPeakAlignedGibbsGap w φ τ l ψ ∧
    egbFixedChargeAPeakAlignedGibbsGap w φ τ l ψ ≤ egbFixedChargeAGibbsBarrier w φ τ l :=
  egbFixedChargeAInteriorGibbsGap_bounds w φ τ l (egbFixedChargeAPeakInverseAngle τ φ ψ)

theorem egbFixedChargeAPeakAlignedGibbsGap_center (w φ τ l : ℝ) :
    egbFixedChargeAPeakAlignedGibbsGap w φ τ l 0 = egbFixedChargeAGibbsBarrier w φ τ l := by
  rw [egbFixedChargeAPeakAlignedGibbsGap_formula, egbFixedChargeAPeakAlignedRadius_center]
  rfl

theorem egbFixedChargeAPeakAlignedGibbsGap_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      cos ψ ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAInteriorGibbsGap_uniform_aligned_first_zero_limit w φ l₁ l₂)) ε hε
  filter_upwards [h] with τ hτ
  intro ψ
  simpa only [egbFixedChargeAPeakAlignedGibbsGap, egbFixedChargeAPeakAlignedProfile_inverse] using
    hτ (egbFixedChargeAPeakInverseAngle τ φ ψ)

theorem egbFixedChargeAPeakAlignedGibbsGap_uniform_profile_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ => egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂)
      (fun ψ => cos ψ ^ (4 : ℕ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAPeakAlignedGibbsGap_uniform_first_zero_limit w φ l₁ l₂)) 1 (by norm_num)
  have hd := egbCoexistenceASymmetricRatio_critical_limit.eventually_lt_const hε
  filter_upwards [he, hd] with τ hτ hδ
  intro ψ
  have hp := (egbCoexistenceASymmetricRatio_bounds τ).1
  have h := hτ ψ
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_div, abs_of_pos hp] at h
  have hx := (div_lt_iff₀ hp).mp h
  simp only [one_mul] at hx
  simpa only [Real.dist_eq, abs_sub_comm] using hx.trans hδ

theorem egbFixedChargeAPeakAlignedGibbsGap_moving_first_zero_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ (ψ τ) / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      cos (ψ τ) ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  simpa only [egbFixedChargeAPeakAlignedGibbsGap, egbFixedChargeAPeakAlignedProfile_inverse] using
    egbFixedChargeAInteriorGibbsGap_moving_aligned_first_zero_limit w φ l₁ l₂ (fun τ => egbFixedChargeAPeakInverseAngle τ φ (ψ τ))

theorem egbFixedChargeAPeakAlignedGibbsGap_moving_peak_zero_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ (ψ τ) / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      cos (ψ τ) ^ (4 : ℕ)) / egbFixedChargeAMiddleGapCoordinate τ φ) atBot (𝓝 (0 : ℝ)) := by
  simpa only [egbFixedChargeAPeakAlignedGibbsGap, egbFixedChargeAPeakAlignedProfile_inverse] using
    egbFixedChargeAInteriorGibbsGap_moving_aligned_peak_zero_limit w φ l₁ l₂ (fun τ => egbFixedChargeAPeakInverseAngle τ φ (ψ τ))

end GaloisForLFunctions.HTGeometry
