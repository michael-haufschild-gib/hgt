import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAAlignedForceUniform

/-!
# Uniform energy and derivative control of the aligned Gibbs profile

The actual barrier-normalized potential and its angle derivative have
uniformly vanishing first corrections to cos(psi)^(4 : ℕ) and
-4*sin(psi)*cos(psi)^(3 : ℕ). The derivative estimate also holds along
arbitrary moving angle trajectories, without regularity assumptions.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAPeakNormalizedGibbs_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂ ψ - cos ψ ^ (4 : ℕ)) /
      egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot :=
  egbFixedChargeAPeakAlignedGibbsGap_uniform_first_zero_limit w φ l₁ l₂

theorem egbFixedChargeAPeakNormalizedGibbs_derivative_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ => (deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ + 4 * sin ψ * cos ψ ^ (3 : ℕ)) /
      egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  simpa only [egbFixedChargeAPeakNormalizedGibbs_derivative] using
    egbFixedChargeAPeakNormalizedGibbsForce_uniform_first_zero_limit w φ l₂

theorem egbFixedChargeAPeakNormalizedGibbs_derivative_uniform_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ => deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (fun ψ => -4 * sin ψ * cos ψ ^ (3 : ℕ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_derivative_uniform_first_zero_limit w φ l₁ l₂)) 1 (by norm_num)
  have hd := egbCoexistenceASymmetricRatio_critical_limit.eventually_lt_const hε
  filter_upwards [he, hd] with τ hτ hδ
  intro ψ
  have hp := (egbCoexistenceASymmetricRatio_bounds τ).1
  have h := hτ ψ
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_div, abs_of_pos hp] at h
  have hx := (div_lt_iff₀ hp).mp h
  simp only [one_mul] at hx
  rw [dist_comm, Real.dist_eq]
  have heq : deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ - (-4 * sin ψ * cos ψ ^ (3 : ℕ)) =
      deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ + 4 * sin ψ * cos ψ ^ (3 : ℕ) := by ring
  rw [heq]
  exact hx.trans hδ

theorem egbFixedChargeAPeakNormalizedGibbs_derivative_moving_first_zero_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (ψ τ) + 4 * sin (ψ τ) * cos (ψ τ) ^ (3 : ℕ)) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_derivative_uniform_first_zero_limit w φ l₁ l₂)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [dist_comm] using hτ (ψ τ)

theorem egbFixedChargeAPeakNormalizedGibbs_derivative_moving_peak_zero_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (ψ τ) + 4 * sin (ψ τ) * cos (ψ τ) ^ (3 : ℕ)) /
      egbFixedChargeAMiddleGapCoordinate τ φ) atBot (𝓝 (0 : ℝ)) := by
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have h := (egbFixedChargeAPeakNormalizedGibbs_derivative_moving_first_zero_limit w φ l₁ l₂ ψ).div
    (egbFixedChargeAMiddleGapCoordinate_linear_limit φ) hc.ne
  simp only [zero_div, Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeAPeakNormalizedGibbs_uniform_C1_error_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ =>
      |(egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂ ψ - cos ψ ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ| +
      |(deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ + 4 * sin ψ * cos ψ ^ (3 : ℕ)) /
        egbCoexistenceASymmetricRatio τ|) (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hv := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAPeakNormalizedGibbs_uniform_first_zero_limit w φ l₁ l₂))
    (ε / 3) (by positivity)
  have hd := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAPeakNormalizedGibbs_derivative_uniform_first_zero_limit w φ l₁ l₂))
    (ε / 3) (by positivity)
  filter_upwards [hv, hd] with τ hτ hτ'
  intro ψ
  have hvψ := hτ ψ
  have hdψ := hτ' ψ
  simp only [Real.dist_eq, zero_sub, abs_neg] at hvψ hdψ ⊢
  rw [abs_of_nonneg (by positivity)]
  linarith

theorem egbFixedChargeAPeakNormalizedGibbs_moving_C1_error_limit (w φ l₁ l₂ : ℝ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ =>
      |(egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂ (ψ τ) - cos (ψ τ) ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ| +
      |(deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (ψ τ) + 4 * sin (ψ τ) * cos (ψ τ) ^ (3 : ℕ)) /
        egbCoexistenceASymmetricRatio τ|) atBot (𝓝 (0 : ℝ)) := by
  have hv := (egbFixedChargeAPeakAlignedGibbsGap_moving_first_zero_limit w φ l₁ l₂ ψ).abs
  have hd := (egbFixedChargeAPeakNormalizedGibbs_derivative_moving_first_zero_limit w φ l₁ l₂ ψ).abs
  simpa only [abs_zero, add_zero, egbFixedChargeAPeakNormalizedGibbs] using hv.add hd

end GaloisForLFunctions.HTGeometry
