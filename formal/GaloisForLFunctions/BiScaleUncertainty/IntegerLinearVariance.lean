import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonPositiveCoercivity
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact additive-only integer-window obstruction

The linear signal has an exact mean-square decomposition and adjacent energy.
Its variance-to-energy ratio is the quadratic lower bound for additive coercivity.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- Exact variance decomposition of the integer signal about every real center. -/
theorem sum_Icc_linear_centered_sq (N : ℕ) (c : ℝ) :
    (∑ n ∈ Icc 1 N, ((n : ℝ) - c) ^ 2) =
      (N : ℝ) * (c - ((N : ℝ) + 1) / 2) ^ 2 +
        (N : ℝ) * ((N : ℝ) ^ 2 - 1) / 12 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih]
    push_cast
    ring

/-- The mean of the integer window attains its exact variance. -/
theorem sum_Icc_linear_mean_sq (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((n : ℝ) - ((N : ℝ) + 1) / 2) ^ 2) =
      (N : ℝ) * ((N : ℝ) ^ 2 - 1) / 12 := by
  rw [sum_Icc_linear_centered_sq, sub_self]
  ring

/-- Every center has squared error at least the exact integer-window variance. -/
theorem sum_Icc_linear_centered_sq_lower (N : ℕ) (c : ℝ) :
    (N : ℝ) * ((N : ℝ) ^ 2 - 1) / 12 ≤ ∑ n ∈ Icc 1 N, ((n : ℝ) - c) ^ 2 := by
  rw [sum_Icc_linear_centered_sq]
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))

/-- Each adjacent increment of the integer signal is exactly one. -/
theorem additiveStepEnergy_linear (N : ℕ) :
    additiveStepEnergy N (fun n : ℕ => (n : ℝ)) = ((N - 1 : ℕ) : ℝ) := by
  unfold additiveStepEnergy
  have he (n : ℕ) : (((n + 1 : ℕ) : ℝ) - (n : ℝ)) ^ 2 = 1 := by push_cast; ring
  simp only [he, sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico]

/-- For every nontrivial integer window, additive coercivity requires the exact quadratic ratio. -/
theorem additive_coercivity_constant_linear_lower_bound {N : ℕ} (hN : 2 ≤ N)
    {C : ℝ} (hC : ∀ f : ℕ → ℝ, ∃ c : ℝ,
      (∑ n ∈ Icc 1 N, (f n - c) ^ 2) ≤ C * additiveStepEnergy N f) :
    (N : ℝ) * ((N : ℝ) + 1) / 12 ≤ C := by
  obtain ⟨c, hc⟩ := hC (fun n : ℕ => (n : ℝ))
  have hv := sum_Icc_linear_centered_sq_lower N c
  rw [additiveStepEnergy_linear, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hc
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) - 1 := by linarith only [hNR]
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    _ = (N : ℝ) * ((N : ℝ) ^ 2 - 1) / 12 := by ring
    _ ≤ C * ((N : ℝ) - 1) := hv.trans hc

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
