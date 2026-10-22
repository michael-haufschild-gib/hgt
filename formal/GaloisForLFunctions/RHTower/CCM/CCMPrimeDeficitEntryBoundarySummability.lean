import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEntryBoundaryBounds
import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# Absolute summability of the normalized transient boundary

At the actual entry time `2 * log n`, square-root normalization supplies
one additional factor `1 / n`. The complete transient boundary therefore
has finite absolute mass at the critical scale. The limiting-constant
Möbius term has already been separated and is not included in this claim.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem abs_ccmPrimeDeficitEntryTransient_div_le (n : ℕ) :
    |ccmPrimeDeficitEntryTransient n| / n ≤
      (Real.log n + 14) / (2 * (n : ℝ) ^ 2) := by
  calc
    _ ≤ ((Real.log n + 14) / (2 * n)) / n :=
      div_le_div_of_nonneg_right (abs_ccmPrimeDeficitEntryTransient_le n) (Nat.cast_nonneg n)
    _ = _ := by ring

theorem summable_abs_ccmPrimeDeficitEntryTransient_div :
    Summable (fun n : ℕ => |ccmPrimeDeficitEntryTransient n| / n) := by
  have hp : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hm : Summable (fun n : ℕ => (Real.log n + 14) / (2 * (n : ℝ) ^ 2)) := by
    exact ((Sieve.summable_log_div_sq.mul_left (1 / 2 : ℝ)).add (hp.mul_left 7)).congr
      (fun n => by ring)
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    abs_ccmPrimeDeficitEntryTransient_div_le hm

theorem summable_ccmPrimeDeficitEntryTransient_div :
    Summable (fun n : ℕ => ccmPrimeDeficitEntryTransient n / n) := by
  apply Summable.of_norm_bounded summable_abs_ccmPrimeDeficitEntryTransient_div
  intro n
  simp only [Real.norm_eq_abs, abs_div,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), le_refl]

theorem summable_ccmPrimeDeficitEntryTransient_at_entry_scale :
    Summable (fun n : ℕ => Real.exp (-(2 * Real.log n / 2)) *
      |ccmPrimeDeficitEntryTransient n|) := by
  apply summable_abs_ccmPrimeDeficitEntryTransient_div.congr
  intro n
  by_cases hn : n = 0
  · simp [hn, ccmPrimeDeficitEntryTransient, moebiusCoeff]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [show 2 * Real.log n / 2 = Real.log n by ring, Real.exp_neg, Real.exp_log hnpos]
  ring

theorem sum_abs_ccmPrimeDeficitEntryTransient_div_le_tsum (S : Finset ℕ) :
    (∑ n ∈ S, |ccmPrimeDeficitEntryTransient n| / n) ≤
      ∑' n : ℕ, |ccmPrimeDeficitEntryTransient n| / n :=
  summable_abs_ccmPrimeDeficitEntryTransient_div.sum_le_tsum S (fun n _ => by positivity)

end RHTower
