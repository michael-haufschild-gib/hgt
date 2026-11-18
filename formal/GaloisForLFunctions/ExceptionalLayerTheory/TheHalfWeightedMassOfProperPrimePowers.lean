import GaloisForLFunctions.ExceptionalLayerTheory.BalancedProductsInTheLargePrimeCells
import GaloisForLFunctions.RHTower.PrimeMassSharpUpper
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Harmonic cost of proper prime powers at the square root

The cumulative proper-power Mangoldt mass is of square-root order.
Partial summation against the inverse square root therefore has only
logarithmic cost, even at the endpoint exponent.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem proper_prefix (n : ℕ) :
    (∑ u ∈ Icc 1 n, primePowerPart u) ≤ 3*(Real.log 4+4)*Real.sqrt n := by
  have hi : Icc 1 n = Ioc 0 n := by ext; simp only [mem_Icc,mem_Ioc]; omega
  rw [hi]
  apply le_trans _ (GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt n)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter]
  apply le_of_eq
  exact sum_congr rfl fun u _ => by by_cases h : u.Prime <;> simp [primePowerPart,h]

private theorem sqrt_increment {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt n*((Real.sqrt n)⁻¹-(Real.sqrt (n+1 : ℕ))⁻¹) ≤ 1/(n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sqrt_pos.mpr hn0
  have h := mul_le_mul_of_nonneg_right (mul_inv_sqrt_sub_inv_sqrt_succ_le n hn) hs.le
  rw [inv_mul_cancel₀ hs.ne'] at h
  rw [le_div_iff₀ hn0]
  linarith only [h]

/-- The sum of the proper-power Mangoldt weights divided by the square
root of their arguments is bounded by a constant times one plus log X. -/
theorem proper_power_half_weight (X : ℕ) :
    (∑ u ∈ Icc 1 X, primePowerPart u/Real.sqrt u) ≤ 3*(Real.log 4+4)*(2+Real.log X) := by
  let C := 3*(Real.log 4+4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let P := fun t => ∑ u ∈ Icc 1 t, primePowerPart u
  have hP (t : ℕ) : P (t+1) = P t+primePowerPart (t+1) := sum_Icc_succ_top (by omega) _
  have hc (n : ℕ) (hn : 1 ≤ n) :
      P n/Real.sqrt n - P n/Real.sqrt (n+1 : ℕ) ≤ C*(1/(n : ℝ)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h₁ := Real.sqrt_pos.mpr hn0
    have h₂ := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n+1 : ℕ) by exact_mod_cast Nat.le_succ n)
    have hi := (inv_le_inv₀ (h₁.trans_le h₂) h₁).mpr h₂
    have h := mul_le_mul_of_nonneg_right (proper_prefix n) (sub_nonneg.mpr hi)
    have hh := mul_le_mul_of_nonneg_left (sqrt_increment hn) hC
    calc _ = P n*((Real.sqrt n)⁻¹-(Real.sqrt (n+1 : ℕ))⁻¹) := by ring
         _ ≤ (C*Real.sqrt n)*_ := h
         _ ≤ _ := by simpa only [mul_assoc] using hh
  have main (n : ℕ) : (∑ u ∈ Icc 1 (n+1), primePowerPart u/Real.sqrt u) ≤
      P (n+1)/Real.sqrt (n+1 : ℕ)+C*∑ j ∈ Icc 1 n, 1/(j : ℝ) := by
    induction n with
    | zero => simp [P]
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega) (fun u => primePowerPart u/Real.sqrt u),hP (n+1),
        add_div,sum_Icc_succ_top (by omega) (fun j => 1/(j : ℝ)),mul_add]
      linarith only [ih,hc (n+1) (Nat.succ_pos n)]
  rcases X with _ | n
  · simp only [Icc_eq_empty_of_lt (Nat.zero_lt_one),sum_empty,Nat.cast_zero,Real.log_zero,add_zero]
    positivity
  have hs := Real.sqrt_pos.mpr (show (0 : ℝ) < (n+1 : ℕ) by positivity)
  have hb : P (n+1)/Real.sqrt (n+1 : ℕ) ≤ C := (div_le_iff₀ hs).mpr (proper_prefix _)
  have hh := (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.le_succ n))
    (f := fun j : ℕ => 1/(j : ℝ)) (fun _ _ _ => by positivity)).trans (Sieve.sum_Icc_one_div_le_one_add_log (n+1))
  exact (main n).trans ((add_le_add hb (mul_le_mul_of_nonneg_left hh hC)).trans_eq (by change _=C*(2+_); ring))

#print axioms proper_power_half_weight
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
