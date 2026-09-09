import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakGibbsJetIdentity
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAAlignedAngularJetLimits

/-!
# All-order uniform aligned Gibbs asymptotics

For each natural derivative order, the actual normalized Gibbs profile
has a uniformly vanishing first correction to cos(psi)^4. The result
holds over all real angles and along arbitrary moving angle choices.
Uniformity is asserted for each fixed order, without claiming one
bound simultaneously uniform in unbounded derivative order.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) :
    TendstoUniformly (fun τ ψ => (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
      iteratedDeriv n (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  cases n with
  | zero => simpa only [iteratedDeriv_zero] using egbFixedChargeAPeakNormalizedGibbs_uniform_first_zero_limit w φ l₁ l₂
  | succ n =>
      simpa only [Nat.succ_eq_add_one, egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_correction] using
        egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_uniform_zero_limit w φ l₂ n

theorem egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_limit (w φ l₁ l₂ : ℝ) (n : ℕ) :
    TendstoUniformly (fun τ ψ => iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (iteratedDeriv n (fun x : ℝ => cos x ^ 4)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ n)) 1 (by norm_num)
  have hd := egbCoexistenceASymmetricRatio_critical_limit.eventually_lt_const hε
  filter_upwards [he, hd] with τ hτ hδ
  intro ψ
  have hp := (egbCoexistenceASymmetricRatio_bounds τ).1
  have h := hτ ψ
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_div, abs_of_pos hp] at h
  have hx := (div_lt_iff₀ hp).mp h
  simp only [one_mul] at hx
  simpa only [Real.dist_eq, abs_sub_comm] using hx.trans hδ

theorem egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_moving_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (ψ τ) -
      iteratedDeriv n (fun x : ℝ => cos x ^ 4) (ψ τ)) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ n)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [dist_comm] using hτ (ψ τ)

theorem egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_moving_peak_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (ψ τ) -
      iteratedDeriv n (fun x : ℝ => cos x ^ 4) (ψ τ)) / egbFixedChargeAMiddleGapCoordinate τ φ) atBot (𝓝 (0 : ℝ)) := by
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have h := (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_moving_first_zero_limit w φ l₁ l₂ n ψ).div
    (egbFixedChargeAMiddleGapCoordinate_linear_limit φ) hc.ne
  simp only [zero_div, Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
