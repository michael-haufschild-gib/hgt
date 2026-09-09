import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakGibbsC1Profile

/-!
# Mirror symmetry of the aligned physical energy and slope

Unlike mirrors about the phase mean, mirrors in the exact moving-peak
coordinate have no fifth-order actual Gibbs-energy difference. Their
normalized slopes are opposite through the first correction. Both
statements permit arbitrary moving mirror coordinates.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakGibbsMirrorDifference (w φ τ l ψ : ℝ) : ℝ :=
  egbFixedChargeAPeakAlignedGibbsGap w φ τ l ψ - egbFixedChargeAPeakAlignedGibbsGap w φ τ l (-ψ)

theorem egbFixedChargeAPeakGibbsMirrorDifference_formula (w φ τ l ψ : ℝ) :
    egbFixedChargeAPeakGibbsMirrorDifference w φ τ l ψ =
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAPeakAlignedRadius w φ τ ψ) -
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAPeakAlignedRadius w φ τ (-ψ)) := by
  unfold egbFixedChargeAPeakGibbsMirrorDifference
  rw [egbFixedChargeAPeakAlignedGibbsGap_formula, egbFixedChargeAPeakAlignedGibbsGap_formula]
  ring

theorem egbFixedChargeAPeakGibbsMirrorDifference_uniform_normalized_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAPeakGibbsMirrorDifference w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂) /
      egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAPeakAlignedGibbsGap_uniform_first_zero_limit w φ l₁ l₂))
    (ε / 3) (by positivity)
  filter_upwards [he] with τ hτ
  intro ψ
  have hp := hτ ψ
  have hn := hτ (-ψ)
  simp only [Real.dist_eq, zero_sub, abs_neg] at hp hn ⊢
  have hf : (egbFixedChargeAPeakGibbsMirrorDifference w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂) / egbCoexistenceASymmetricRatio τ =
      (egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ - cos ψ ^ 4) / egbCoexistenceASymmetricRatio τ -
      (egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ (-ψ) / egbFixedChargeAGibbsBarrier w φ τ l₂ - cos (-ψ) ^ 4) / egbCoexistenceASymmetricRatio τ := by
    unfold egbFixedChargeAPeakGibbsMirrorDifference
    rw [cos_neg]
    ring
  rw [hf]
  calc
    _ ≤ |(egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ - cos ψ ^ 4) / egbCoexistenceASymmetricRatio τ| +
        |-((egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ (-ψ) / egbFixedChargeAGibbsBarrier w φ τ l₂ - cos (-ψ) ^ 4) /
          egbCoexistenceASymmetricRatio τ)| := abs_add_le _ _
    _ < ε := by rw [abs_neg]; linarith

theorem egbFixedChargeAPeakGibbsMirrorDifference_moving_normalized_zero_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (egbFixedChargeAPeakGibbsMirrorDifference w φ τ l₁ (ψ τ) / egbFixedChargeAGibbsBarrier w φ τ l₂) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakGibbsMirrorDifference_uniform_normalized_zero_limit w φ l₁ l₂)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [dist_comm] using hτ (ψ τ)

theorem egbFixedChargeAPeakGibbsMirrorDifference_moving_fifth_zero_limit (w φ l : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => egbFixedChargeAPeakGibbsMirrorDifference w φ τ l (ψ τ) / egbCoexistenceASymmetricRatio τ ^ 5)
      atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAPeakGibbsMirrorDifference_moving_normalized_zero_limit w φ l l ψ).mul
    (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l)
  simp only [zero_mul] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hb := egbFixedChargeAGibbsBarrier_pos w φ τ l
  field_simp <;> ring

theorem egbFixedChargeAPeakNormalizedGibbs_derivative_moving_odd_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (ψ τ) +
      deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (-ψ τ)) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAPeakNormalizedGibbs_derivative_moving_first_zero_limit w φ l₁ l₂ ψ).add
    (egbFixedChargeAPeakNormalizedGibbs_derivative_moving_first_zero_limit w φ l₁ l₂ (fun τ => -ψ τ))
  simp only [add_zero, sin_neg, cos_neg] at h
  convert h using 1
  funext τ
  ring

end GaloisForLFunctions.HTGeometry
