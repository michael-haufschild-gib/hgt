import GaloisForLFunctions.RHTower.Sieve.CoprimeHarmonicCentering
import GaloisForLFunctions.RHTower.Sieve.HarmonicFloorDefect

/-!
# The harmonic bridge and the centered divisor-indexed defect

The coprime decomposition is written with the interval harmonic sum `∑_{j ≤ n} 1/j` while the
harmonic comparison of the tree is stated for `harmonic n`.  This module bridges the two and then
bounds the centered divisor-indexed sum of the coprime harmonic decomposition by `4 d(e)/z`.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

theorem harmonic_eq_sum_Icc (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ j ∈ Finset.Icc 1 n, 1 / (j : ℝ) := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih =>
    rw [harmonic_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rw [← ih]
    push_cast
    ring

/-- **The centered divisor-indexed defect.**  Each divisor contributes at most `4/z`. -/
theorem abs_coprime_centered_term_le {z f : ℕ} (hf : 1 ≤ f) (hfz : f ≤ z) :
    |((μ f : ℤ) : ℝ) / (f : ℝ) *
        ((∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ))
          - (Real.log (z : ℝ) + Real.eulerMascheroniConstant) + Real.log (f : ℝ))|
      ≤ 4 / (z : ℝ) := by
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast (by omega : 0 < f)
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hm : 1 ≤ z / f := (Nat.one_le_div_iff (by omega)).mpr hfz
  have hmR : (0 : ℝ) < ((z / f : ℕ) : ℝ) := by exact_mod_cast hm
  have hdefect := abs_harmonic_floor_defect_le hf hfz
  rw [harmonic_eq_sum_Icc] at hdefect
  have hlog : Real.log ((z : ℝ) / (f : ℝ)) = Real.log (z : ℝ) - Real.log (f : ℝ) :=
    Real.log_div (ne_of_gt hzR) (ne_of_gt hfR)
  rw [hlog] at hdefect
  have hrw : (∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ))
      - (Real.log (z : ℝ) + Real.eulerMascheroniConstant) + Real.log (f : ℝ)
      = (∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ))
        - (Real.log (z : ℝ) - Real.log (f : ℝ)) - Real.eulerMascheroniConstant := by
    ring
  rw [hrw, abs_mul]
  have hmu : |((μ f : ℤ) : ℝ) / (f : ℝ)| ≤ 1 / (f : ℝ) := by
    rw [abs_div, abs_of_pos hfR]
    exact div_le_div_of_nonneg_right (abs_moebius_le_one f) hfR.le
  have hchain : (2 : ℝ) / ((z / f : ℕ) : ℝ) ≤ 4 * (f : ℝ) / (z : ℝ) := by
    rw [div_le_div_iff₀ hmR hzR]
    have hnat : z ≤ 2 * (z / f) * f := two_mul_natDiv_mul_ge hf hfz
    have hcast : (z : ℝ) ≤ 2 * ((z / f : ℕ) : ℝ) * (f : ℝ) := by exact_mod_cast hnat
    nlinarith [hcast, hmR, hfR]
  calc |((μ f : ℤ) : ℝ) / (f : ℝ)| *
        |(∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ))
          - (Real.log (z : ℝ) - Real.log (f : ℝ)) - Real.eulerMascheroniConstant|
      ≤ (1 / (f : ℝ)) * (2 / ((z / f : ℕ) : ℝ)) :=
        mul_le_mul hmu hdefect (abs_nonneg _) (by positivity)
    _ ≤ (1 / (f : ℝ)) * (4 * (f : ℝ) / (z : ℝ)) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = 4 / (z : ℝ) := by field_simp

/-- **The summed centered defect.** -/
theorem abs_coprime_centered_sum_le {e z : ℕ} (he : 0 < e) (hez : e ≤ z) :
    |∑ f ∈ e.divisors, ((μ f : ℤ) : ℝ) / (f : ℝ) *
        ((∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ))
          - (Real.log (z : ℝ) + Real.eulerMascheroniConstant) + Real.log (f : ℝ))|
      ≤ (e.divisors.card : ℝ) * (4 / (z : ℝ)) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ f ∈ e.divisors,
      |((μ f : ℤ) : ℝ) / (f : ℝ) *
        ((∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ))
          - (Real.log (z : ℝ) + Real.eulerMascheroniConstant) + Real.log (f : ℝ))|
        ≤ 4 / (z : ℝ) := by
    intro f hf
    have hf0 : 0 < f := Nat.pos_of_mem_divisors hf
    have hfe : f ≤ e := Nat.le_of_dvd he (Nat.dvd_of_mem_divisors hf)
    exact abs_coprime_centered_term_le hf0 (le_trans hfe hez)
  simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hterm

end RHTower.Sieve
