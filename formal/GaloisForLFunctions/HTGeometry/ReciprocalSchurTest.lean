import GaloisForLFunctions.HTGeometry.WeightedSchurTest

/-!
# Reciprocal edge weights for the Schur test

A permutation correlation is bounded by its forward and reverse edge weights.
Reciprocity suffices; the weights need not be ratios of vertex weights.
-/

set_option autoImplicit false
open Finset
namespace GaloisForLFunctions

/-- Reciprocal edge weights give the weighted arithmetic–geometric inequality. -/
theorem two_mul_le_reciprocal_weight (a b p q : ℝ) (hp : 0 < p) (hpq : p * q = 1) :
    2 * a * b ≤ p * a ^ 2 + q * b ^ 2 := by
  have hs : 0 ≤ p * (p * a ^ 2 + q * b ^ 2 - 2 * a * b) := by
    calc
      _ = (p * a - b) ^ 2 := by
        calc
          _ = (p * a) ^ 2 + (p * q) * b ^ 2 - 2 * p * a * b := by ring
          _ = _ := by rw [hpq]; ring
      _ ≥ 0 := sq_nonneg _
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hs)

/-- Weighted Young's inequality summed along a permutation and its inverse. -/
theorem permutation_correlation_le_reciprocal_weights {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) (b c : ι → ℝ) (ψ : ι → ι → ℝ)
    (hc : ∀ a, 0 ≤ c a) (hinv : ∀ a, c (e a) = c a)
    (hψ : ∀ a d, 0 < ψ a d) (hrec : ∀ a d, ψ a d * ψ d a = 1) :
    2 * (∑ a, c a * b a * b (e a)) ≤
      ∑ a, b a ^ 2 * c a * (ψ a (e a) + ψ a (e.symm a)) := by
  have hpoint (a : ι) : 2 * (c a * b a * b (e a)) ≤
      c a * (ψ a (e a) * b a ^ 2 + ψ (e a) a * b (e a) ^ 2) := by
    nlinarith only [mul_le_mul_of_nonneg_left
      (two_mul_le_reciprocal_weight (b a) (b (e a))
        (ψ a (e a)) (ψ (e a) a) (hψ a (e a)) (hrec a (e a))) (hc a)]
  have hsecond : (∑ a, c a * (ψ (e a) a * b (e a) ^ 2)) =
      ∑ a, c a * (ψ a (e.symm a) * b a ^ 2) := by
    rw [← Equiv.sum_comp e (fun a => c a * (ψ a (e.symm a) * b a ^ 2))]
    simp only [hinv, Equiv.symm_apply_apply]
  calc
    _ ≤ ∑ a, c a * (ψ a (e a) * b a ^ 2 + ψ (e a) a * b (e a) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun a _ => hpoint a
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, hsecond]
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring

end GaloisForLFunctions
