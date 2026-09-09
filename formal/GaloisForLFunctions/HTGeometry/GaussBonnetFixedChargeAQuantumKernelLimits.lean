import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQuantumFeature

/-!
# Actual Gibbs convergence to the corpus quantum fidelity kernel

The actual normalized Gibbs barrier converges to the genuine two-copy
quantum fidelity profile. Every fixed derivative has a uniformly
vanishing first correction. Entrywise convergence is uniform over
all pairs of input angles, not only one chosen reference angle.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAQuantumCriticalProfile (ψ : ℝ) : ℝ :=
  (QuantumAlg.quantumKernel egbFixedChargeAPairQubitFeature ψ 0).re

theorem egbFixedChargeAQuantumCriticalProfile_formula (ψ : ℝ) :
    egbFixedChargeAQuantumCriticalProfile ψ = cos ψ ^ 4 := by
  simp only [egbFixedChargeAQuantumCriticalProfile, egbFixedChargeAPairQubitFeature_kernel_real, sub_zero]

theorem egbFixedChargeAGibbs_quantum_jet_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) :
    TendstoUniformly (fun τ ψ =>
      (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
       iteratedDeriv n egbFixedChargeAQuantumCriticalProfile ψ) / egbCoexistenceASymmetricRatio τ)
      (fun _ => (0 : ℝ)) atBot := by
  have h : egbFixedChargeAQuantumCriticalProfile = fun ψ => cos ψ ^ 4 :=
    funext egbFixedChargeAQuantumCriticalProfile_formula
  rw [h]
  exact egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ n

theorem egbFixedChargeAGibbs_quantum_jet_uniform_limit (w φ l₁ l₂ : ℝ) (n : ℕ) :
    TendstoUniformly (fun τ ψ => iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ)
      (iteratedDeriv n egbFixedChargeAQuantumCriticalProfile) atBot := by
  have h : egbFixedChargeAQuantumCriticalProfile = fun ψ => cos ψ ^ 4 :=
    funext egbFixedChargeAQuantumCriticalProfile_formula
  rw [h]
  exact egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_limit w φ l₁ l₂ n

theorem egbFixedChargeAGibbs_quantum_jet_moving_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ =>
      (iteratedDeriv n (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) (ψ τ) -
       iteratedDeriv n egbFixedChargeAQuantumCriticalProfile (ψ τ)) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (0 : ℝ)) := by
  have h : egbFixedChargeAQuantumCriticalProfile = fun ψ => cos ψ ^ 4 :=
    funext egbFixedChargeAQuantumCriticalProfile_formula
  rw [h]
  exact egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_moving_first_zero_limit w φ l₁ l₂ n ψ

theorem egbFixedChargeAGibbs_quantum_kernel_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ (p : ℝ × ℝ) =>
      (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂ (p.1 - p.2) -
       (QuantumAlg.quantumKernel egbFixedChargeAPairQubitFeature p.1 p.2).re) /
        egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_uniform_first_zero_limit w φ l₁ l₂)) ε hε
  filter_upwards [h] with τ hτ
  intro p
  simpa only [egbFixedChargeAPairQubitFeature_kernel_real] using hτ (p.1 - p.2)

end GaloisForLFunctions.HTGeometry
