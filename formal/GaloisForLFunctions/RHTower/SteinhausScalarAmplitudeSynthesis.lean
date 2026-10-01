import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.WeightedPortCapacity

open Finset Complex
open scoped ComplexConjugate
noncomputable section
namespace RHTower
open HTGeometry.ConstraintMotiveRelativity

/-- Conjugate-amplitude biases have the exact reciprocal energy cost and preserve
uniform mode accuracy through positive normalized amplitude weights. -/
theorem exists_finiteScalarAmplitudeBiases {ι : Type*} (P : Finset ι) (a : ι → ℂ)
    (hE : 0 < ∑ p ∈ P, ‖a p‖ ^ 2) (γ : ℂ) :
    ∃ μ : ι → ℂ, (∀ p ∉ P, μ p = 0) ∧ (∑ p ∈ P, μ p * a p) = γ ∧
      (∑ p ∈ P, ‖μ p‖ ^ 2) = ‖γ‖ ^ 2 / (∑ p ∈ P, ‖a p‖ ^ 2) ∧
      (∀ p ∈ P, ‖μ p‖ = ‖γ‖ * ‖a p‖ / (∑ q ∈ P, ‖a q‖ ^ 2)) ∧
      ∀ (v : ι → ℂ) (g : ℂ) (ε : ℝ), (∀ p ∈ P, ‖v p - g‖ ≤ ε) →
        ‖(∑ p ∈ P, μ p * (a p * v p)) - γ * g‖ ≤ ‖γ‖ * ε := by
  classical
  let E : ℝ := ∑ p ∈ P, ‖a p‖ ^ 2
  have hC : portCap (fun _ : ι => (1 : ℝ)) a P = E := by simp [portCap, E]
  have hCne : portCap (fun _ : ι => (1 : ℝ)) a P ≠ 0 := by rw [hC]; exact hE.ne'
  let μ := portMinimizer (fun _ : ι => (1 : ℝ)) a P γ
  have hμ (p : ι) (hp : p ∈ P) : μ p = γ * conj (a p) / (E : ℂ) := by
    simp [μ, portMinimizer, hp, hC]
  have hmean : (∑ p ∈ P, μ p * a p) = γ := by
    simpa only [portValue, mul_comm] using
      portValue_portMinimizer (fun _ : ι => (show (0 : ℝ) < 1 by norm_num)) hCne γ
  have hcost : (∑ p ∈ P, ‖μ p‖ ^ 2) = ‖γ‖ ^ 2 / E := by
    simpa only [portEnergy, one_mul, hC] using
      portEnergy_portMinimizer (fun _ : ι => (show (0 : ℝ) < 1 by norm_num)) hCne γ
  have hnorm (p : ι) (hp : p ∈ P) : ‖μ p‖ = ‖γ‖ * ‖a p‖ / E := by
    rw [hμ p hp, norm_div, norm_mul, Complex.norm_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE]
  have hEne : E ≠ 0 := hE.ne'
  have hmass : (∑ p ∈ P, ‖μ p‖ * ‖a p‖) = ‖γ‖ := by
    calc
      _ = ∑ p ∈ P, (‖γ‖ / E) * ‖a p‖ ^ 2 := by
        apply sum_congr rfl
        intro p hp
        rw [hnorm p hp]
        ring
      _ = (‖γ‖ / E) * E := by rw [← mul_sum]
      _ = ‖γ‖ := by field_simp [hEne]
  refine ⟨μ, ?_, hmean, hcost, hnorm, ?_⟩
  · intro p hp
    simp [μ, portMinimizer, hp]
  · intro v g ε hv
    have heq : (∑ p ∈ P, μ p * (a p * v p)) - γ * g =
        ∑ p ∈ P, (μ p * a p) * (v p - g) := by
      rw [← hmean, sum_mul, ← sum_sub_distrib]
      apply sum_congr rfl
      intro p _
      ring
    rw [heq]
    calc
      _ ≤ ∑ p ∈ P, ‖(μ p * a p) * (v p - g)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ P, (‖μ p‖ * ‖a p‖) * ε := by
        apply sum_le_sum
        intro p hp
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hv p hp) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (∑ p ∈ P, ‖μ p‖ * ‖a p‖) * ε := (sum_mul ..).symm
      _ = ‖γ‖ * ε := by rw [hmass]

end RHTower
