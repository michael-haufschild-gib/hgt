import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Exact first and second moments of finite harmonic tails

Adding the final reciprocal shifts every old tail by the same amount. The first
moment is the horizon, and its square-moment recurrence gives `2N-H_N` exactly.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

theorem sum_harmonic_tails (N : ℕ) :
    (∑ k ∈ range N, ((harmonic N : ℝ) - harmonic k)) = N := by
  induction N with
  | zero => simp only [sum_range_zero, Nat.cast_zero]
  | succ N ih =>
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    rw [sum_range_succ, harmonic_succ]
    push_cast
    simp only [show ∀ k : ℕ, (harmonic N : ℝ) + ((N : ℝ) + 1)⁻¹ - harmonic k =
        ((harmonic N : ℝ) - harmonic k) + ((N : ℝ) + 1)⁻¹ from fun k => by ring,
      sum_add_distrib, ih, sum_const, card_range, nsmul_eq_mul]
    field_simp [hN]
    ring

/-- The squared harmonic tails have exactly linear total mass. -/
theorem sum_sq_harmonic_tails (N : ℕ) :
    (∑ k ∈ range N, ((harmonic N : ℝ) - harmonic k) ^ 2) =
      2 * (N : ℝ) - harmonic N := by
  induction N with
  | zero => simp only [sum_range_zero, Nat.cast_zero, harmonic_zero, Rat.cast_zero,
      mul_zero, sub_zero]
  | succ N ih =>
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    rw [sum_range_succ, harmonic_succ]
    push_cast
    have hterm (k : ℕ) :
        ((harmonic N : ℝ) + ((N : ℝ) + 1)⁻¹ - harmonic k) ^ 2 =
          ((harmonic N : ℝ) - harmonic k) ^ 2 +
            2 * ((N : ℝ) + 1)⁻¹ * ((harmonic N : ℝ) - harmonic k) +
            (((N : ℝ) + 1)⁻¹) ^ 2 := by ring
    simp only [hterm, sum_add_distrib, ← mul_sum, ih, sum_harmonic_tails,
      sum_const, card_range, nsmul_eq_mul]
    field_simp [hN]
    ring

/-- Reversing the horizon gives the boundary-layer form of the same identity. -/
theorem sum_sq_harmonic_boundary_tails (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((harmonic N : ℝ) - harmonic (N - n)) ^ 2) =
      2 * (N : ℝ) - harmonic N := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, ← Nat.sub_sub]
  rw [sum_range_reflect (fun k => ((harmonic N : ℝ) - harmonic k) ^ 2),
    sum_sq_harmonic_tails]

end GaloisForLFunctions.HTGeometry

