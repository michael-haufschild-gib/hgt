import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsAngleMeans

/-!
# Exact vanishing angular means of every positive Gibbs derivative

The actual aligned Gibbs energy is smooth and periodic before taking
any critical limit. Every derivative has the same period, so the
fundamental theorem of calculus gives zero uniform-angle mean for
all positive derivative orders at every coexistence state.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology ContDiff
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAPeakNormalizedGibbs_periodic (w φ τ l₁ l₂ : ℝ) :
    Function.Periodic (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (2 * Real.pi) := by
  intro ψ
  simp only [egbFixedChargeAPeakNormalizedGibbs, egbFixedChargeAPeakAlignedGibbsGap,
    egbFixedChargeAPeakInverseAngle, egbFixedChargeAPeakInverseCoordinate_formula, sin_add_two_pi]

theorem egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_periodic (w φ τ l₁ l₂ : ℝ) (n : ℕ) :
    Function.Periodic (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂)) (2 * Real.pi) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using egbFixedChargeAPeakNormalizedGibbs_periodic w φ τ l₁ l₂
  | succ n ih =>
      rw [iteratedDeriv_succ]
      intro ψ
      have hf : (fun x => iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (x + 2 * Real.pi)) =
          iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) := funext ih
      have h := deriv_comp_add_const (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂)) (2 * Real.pi) ψ
      rw [hf] at h
      exact h.symm

theorem egbFixedChargeAGibbsAngleJet_period_integral_zero (w φ τ l₁ l₂ : ℝ) (n : ℕ) :
    (∫ ψ in (-Real.pi)..Real.pi, iteratedDeriv (n + 1) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ) = 0 := by
  have hs := egbFixedChargeAPeakNormalizedGibbs_contDiff w φ τ l₁ l₂
  have hd := hs.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)
  have hc := hs.continuous_iteratedDeriv (n + 1)
    (by exact_mod_cast (le_top : (↑(n + 1) : ℕ∞) ≤ ⊤))
  rw [iteratedDeriv_succ] at hc ⊢
  have he := egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_periodic w φ τ l₁ l₂ n (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at he
  rw [intervalIntegral.integral_deriv_eq_sub (fun ψ _ => hd ψ) (hc.intervalIntegrable (-Real.pi) Real.pi), he, sub_self]

theorem egbFixedChargeAGibbsAngleJet_mean_zero (w φ τ l₁ l₂ : ℝ) (n : ℕ) :
    (∫ ψ, iteratedDeriv (n + 1) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ ∂QuantumAlg.unifAngle) = 0 := by
  unfold QuantumAlg.unifAngle
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]),
    egbFixedChargeAGibbsAngleJet_period_integral_zero]
  simp only [smul_zero]

end GaloisForLFunctions.HTGeometry
