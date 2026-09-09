import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQuantumKernelLimits

/-!
# Uniform-angle means of the actual Gibbs profile

The quantum-kernel library provides a probability measure on [-pi,pi]
and its exact quartic cosine mean 3/8. All actual Gibbs derivatives
are integrable for this measure. Their averaged critical errors retain
the o(d) cancellation, and the actual energy mean tends to3/8.
This is a specified angular average, not a thermodynamic ensemble.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology ContDiff
namespace GaloisForLFunctions.HTGeometry

private theorem continuous_integrable_quantum_angle {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f QuantumAlg.unifAngle := by
  unfold QuantumAlg.unifAngle
  apply hf.integrableOn_Icc.smul_measure
  apply ENNReal.inv_ne_top.mpr
  exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne'

theorem egbFixedChargeAGibbsAngleJet_integrable (w φ τ l₁ l₂ : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂)) QuantumAlg.unifAngle := by
  apply continuous_integrable_quantum_angle
  exact (egbFixedChargeAPeakNormalizedGibbs_contDiff w φ τ l₁ l₂).continuous_iteratedDeriv n
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

theorem egbFixedChargeAQuarticAngleJet_integrable (n : ℕ) :
    Integrable (iteratedDeriv n (fun x : ℝ => cos x ^ 4)) QuantumAlg.unifAngle := by
  apply continuous_integrable_quantum_angle
  have h : ContDiff ℝ ∞ (fun x : ℝ => cos x ^ 4) := by fun_prop
  exact h.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

theorem egbFixedChargeAGibbsAngleJet_correction_integrable (w φ τ l₁ l₂ : ℝ) (n : ℕ) :
    Integrable (fun ψ => (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
      iteratedDeriv n (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ) QuantumAlg.unifAngle := by
  exact ((egbFixedChargeAGibbsAngleJet_integrable w φ τ l₁ l₂ n).sub
    (egbFixedChargeAQuarticAngleJet_integrable n)).div_const _

theorem egbFixedChargeAGibbsAngleJet_integrated_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) :
    Tendsto (fun τ => ∫ ψ, (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
      iteratedDeriv n (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ ∂QuantumAlg.unifAngle)
      atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ n)) (ε / 2) he
  filter_upwards [h] with τ hτ
  have hb := norm_integral_le_of_norm_le_const (μ := QuantumAlg.unifAngle)
    (f := fun ψ => (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
      iteratedDeriv n (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ)
    (C := ε / 2) (ae_of_all _ (fun ψ => by
      have hψ := (hτ ψ).le
      simpa only [Real.dist_eq, zero_sub, abs_neg, Real.norm_eq_abs] using hψ))
  have hm : QuantumAlg.unifAngle.real univ = 1 := by simp
  rw [hm, mul_one] at hb
  rw [dist_zero_right]
  exact hb.trans_lt (by linarith)

theorem egbFixedChargeAGibbsAngleJet_mean_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) :
    Tendsto (fun τ => ((∫ ψ, iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ ∂QuantumAlg.unifAngle) -
      (∫ ψ, iteratedDeriv n (fun x : ℝ => cos x ^ 4) ψ ∂QuantumAlg.unifAngle)) /
        egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  have h := egbFixedChargeAGibbsAngleJet_integrated_first_zero_limit w φ l₁ l₂ n
  have heq : (fun τ => ∫ ψ, (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
      iteratedDeriv n (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ ∂QuantumAlg.unifAngle) =
      fun τ => ((∫ ψ, iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ ∂QuantumAlg.unifAngle) -
      (∫ ψ, iteratedDeriv n (fun x : ℝ => cos x ^ 4) ψ ∂QuantumAlg.unifAngle)) / egbCoexistenceASymmetricRatio τ := by
    funext τ
    rw [integral_div, integral_sub (egbFixedChargeAGibbsAngleJet_integrable w φ τ l₁ l₂ n)
      (egbFixedChargeAQuarticAngleJet_integrable n)]
  rw [heq] at h
  exact h

def egbFixedChargeAGibbsAngleMean (w φ τ l₁ l₂ : ℝ) : ℝ :=
  ∫ ψ, egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂ ψ ∂QuantumAlg.unifAngle

theorem egbFixedChargeAGibbsAngleMean_first_zero_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsAngleMean w φ τ l₁ l₂ - 3 / 8) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  simpa only [iteratedDeriv_zero, QuantumAlg.integral_cos_pow4_unifAngle, egbFixedChargeAGibbsAngleMean] using
    egbFixedChargeAGibbsAngleJet_mean_first_zero_limit w φ l₁ l₂ 0

theorem egbFixedChargeAGibbsAngleMean_critical_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsAngleMean w φ τ l₁ l₂) atBot (𝓝 (3 / 8 : ℝ)) := by
  have h := (egbFixedChargeAGibbsAngleMean_first_zero_limit w φ l₁ l₂).mul
    egbCoexistenceASymmetricRatio_critical_limit
  have he : Tendsto (fun τ => egbFixedChargeAGibbsAngleMean w φ τ l₁ l₂ - 3 / 8) atBot (𝓝 (0 : ℝ)) := by
    convert h using 1
    · funext τ
      have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
      field_simp [hd.ne']
    · ring
  simpa only [sub_add_cancel, zero_add] using he.add_const (3 / 8 : ℝ)

end GaloisForLFunctions.HTGeometry
