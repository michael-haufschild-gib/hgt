import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakGibbsAllOrderLimits
import GaloisForLFunctions.HTGeometry.ModulatedWeightSeminorm

/-!
# Harmonic structure of the aligned critical Gibbs profile

The limiting profile contains exactly the constant, frequency-two,
and frequency-four cosine modes. The existing modulation derivative
recurrences give its entire positive-order jet without numerical
expansion. This is a consequence of the actual Gibbs critical limit,
not an assertion of a finite-state trigonometric Gibbs potential.
-/
noncomputable section
open Real Filter Set
open scoped Topology ContDiff
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAQuarticProfile_harmonic_decomposition (ψ : ℝ) :
    cos ψ ^ 4 = 3 / 8 + ((1 / 2 : ℝ) * cos (2 * ψ) + (1 / 8 : ℝ) * cos (4 * ψ)) := by
  simp only [show 4 * ψ = 2 * (2 * ψ) by ring, cos_two_mul]
  ring

theorem egbFixedChargeAQuarticProfile_harmonic_jet (n : ℕ) (ψ : ℝ) :
    iteratedDeriv (n + 1) (fun x : ℝ => cos x ^ 4) ψ =
      (1 / 2 : ℝ) * iteratedDeriv (n + 1) (fun x : ℝ => cos (2 * x)) ψ +
      (1 / 8 : ℝ) * iteratedDeriv (n + 1) (fun x : ℝ => cos (4 * x)) ψ := by
  have hf : (fun x : ℝ => cos x ^ 4) = fun x =>
      3 / 8 + ((1 / 2 : ℝ) * cos (2 * x) + (1 / 8 : ℝ) * cos (4 * x)) :=
    funext egbFixedChargeAQuarticProfile_harmonic_decomposition
  have h₂ : ContDiffAt ℝ (n + 1) (fun x : ℝ => (1 / 2 : ℝ) * cos (2 * x)) ψ := by fun_prop
  have h₄ : ContDiffAt ℝ (n + 1) (fun x : ℝ => (1 / 8 : ℝ) * cos (4 * x)) ψ := by fun_prop
  have ha := _root_.iteratedDeriv_add h₂ h₄
  change iteratedDeriv (n + 1) (fun x : ℝ => (1 / 2 : ℝ) * cos (2 * x) + (1 / 8 : ℝ) * cos (4 * x)) ψ = _ at ha
  rw [hf, _root_.iteratedDeriv_const_add (Nat.succ_pos n), ha,
    _root_.iteratedDeriv_const_mul_field, _root_.iteratedDeriv_const_mul_field]

theorem egbFixedChargeAQuarticMode_two_step (a : ℝ) (n : ℕ) (ψ : ℝ) :
    iteratedDeriv (n + 2) (fun x : ℝ => cos (a * x)) ψ =
      -(a ^ 2) * iteratedDeriv n (fun x : ℝ => cos (a * x)) ψ := by
  rw [show n + 2 = (n + 1) + 1 by omega, iteratedDeriv_cos_mul_succ,
    iteratedDeriv_sin_mul_succ]
  ring

theorem egbFixedChargeAQuarticMode_four_step (a : ℝ) (n : ℕ) (ψ : ℝ) :
    iteratedDeriv (n + 4) (fun x : ℝ => cos (a * x)) ψ =
      a ^ 4 * iteratedDeriv n (fun x : ℝ => cos (a * x)) ψ := by
  rw [show n + 4 = (n + 2) + 2 by omega, egbFixedChargeAQuarticMode_two_step,
    egbFixedChargeAQuarticMode_two_step]
  ring

theorem egbFixedChargeAQuarticProfile_differential_recurrence (n : ℕ) (ψ : ℝ) :
    iteratedDeriv (n + 5) (fun x : ℝ => cos x ^ 4) ψ +
      20 * iteratedDeriv (n + 3) (fun x : ℝ => cos x ^ 4) ψ +
      64 * iteratedDeriv (n + 1) (fun x : ℝ => cos x ^ 4) ψ = 0 := by
  rw [show n + 5 = (n + 4) + 1 by omega, show n + 3 = (n + 2) + 1 by omega]
  rw [egbFixedChargeAQuarticProfile_harmonic_jet, egbFixedChargeAQuarticProfile_harmonic_jet,
    egbFixedChargeAQuarticProfile_harmonic_jet]
  rw [show n + 4 + 1 = (n + 1) + 4 by omega, show n + 2 + 1 = (n + 1) + 2 by omega]
  rw [egbFixedChargeAQuarticMode_four_step, egbFixedChargeAQuarticMode_four_step,
    egbFixedChargeAQuarticMode_two_step, egbFixedChargeAQuarticMode_two_step]
  ring

end GaloisForLFunctions.HTGeometry
