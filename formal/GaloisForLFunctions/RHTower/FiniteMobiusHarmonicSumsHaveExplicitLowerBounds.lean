import GaloisForLFunctions.RHTower.FiniteMobiusHarmonicSumsNeverVanish
import Mathlib.Data.Nat.Factorial.Basic

/-!
Clearing the denominators of a nonzero finite Möbius harmonic sum gives an
explicit lower bound for its real magnitude. The factorial provides a common
denominator at every positive cutoff.
-/

open Finset ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower
set_option autoImplicit false

/-- A common multiple clears every denominator in the finite Möbius harmonic sum. -/
theorem exists_int_mul_sum_moebius_div (N D : ℕ)
    (hD : ∀ d ∈ Icc 1 N, d ∣ D) :
    ∃ z : ℤ, (D : ℝ) * (∑ d ∈ Icc 1 N, (moebius d : ℝ) / d) = z := by
  refine ⟨∑ d ∈ Icc 1 N, moebius d * (D / d : ℕ), ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [mul_sum]
  apply sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < d from (mem_Icc.mp hd).1))
  have hmul : ((D / d : ℕ) : ℝ) * d = D := by
    exact_mod_cast Nat.div_mul_cancel (hD d hd)
  have hquot : (D : ℝ) / d = ((D / d : ℕ) : ℝ) :=
    (div_eq_iff hd0).mpr hmul.symm
  calc
    _ = (moebius d : ℝ) * ((D : ℝ) / d) := by ring
    _ = _ := by rw [hquot]

/-- Nonvanishing and denominator clearing give a real lower bound for every positive common multiple. -/
theorem one_div_le_abs_sum_moebius_div_of_common_multiple
    {N D : ℕ} (hN : 1 ≤ N) (hD0 : 0 < D)
    (hD : ∀ d ∈ Icc 1 N, d ∣ D) :
    1 / (D : ℝ) ≤ |∑ d ∈ Icc 1 N, (moebius d : ℝ) / d| := by
  obtain ⟨z, hz⟩ := exists_int_mul_sum_moebius_div N D hD
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hz0 : z ≠ 0 := by
    intro h
    have hprod := mul_ne_zero hDR.ne' (sum_moebius_div_ne_zero hN)
    apply hprod
    simpa only [h, Int.cast_zero] using hz
  have hzabs : (1 : ℤ) ≤ |z| := by
    rcases lt_or_gt_of_ne hz0 with hneg | hpos
    · rw [abs_of_neg hneg]
      omega
    · rw [abs_of_pos hpos]
      omega
  have hbound : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast hzabs
  rw [← hz, abs_mul, abs_of_pos hDR] at hbound
  exact (div_le_iff₀ hDR).mpr (by simpa only [mul_comm] using hbound)

/-- The factorial is an explicit common denominator, so every positive harmonic sum is at least its reciprocal in absolute value. -/
theorem one_div_factorial_le_abs_sum_moebius_div {N : ℕ} (hN : 1 ≤ N) :
    1 / (N.factorial : ℝ) ≤ |∑ d ∈ Icc 1 N, (moebius d : ℝ) / d| := by
  exact one_div_le_abs_sum_moebius_div_of_common_multiple hN (Nat.factorial_pos N)
    (fun d hd => Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)

#print axioms exists_int_mul_sum_moebius_div
#print axioms one_div_le_abs_sum_moebius_div_of_common_multiple
#print axioms one_div_factorial_le_abs_sum_moebius_div
end RHTower
