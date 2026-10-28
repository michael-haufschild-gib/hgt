import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanCenterKernelIsAHarmonicKernel
import GaloisForLFunctions.HTGeometry.FiniteHarmonicRows

/-!
# Exact cancellation of the center-density row against the pole

The inverse-difference and inverse-sum kernels sum to a single harmonic
boundary term. Restoring the two pole rows cancels the large harmonic bulk;
the remaining ground action is the identity plus an explicit boundary layer.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticCastelnuovoSeveri HTGeometry

/-- The archimedean center kernel on the pole has an exact harmonic row. -/
theorem sum_collarWeight_div_sqrt {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N, collarWeight n j / Real.sqrt j) =
      Real.sqrt n * (((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 -
        3 / (4 * (n : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  rw [← sum_erase_add (Icc 1 N) (fun j => collarWeight n j / Real.sqrt j) hn,
    collarWeight_self, zero_div, add_zero, ← sum_erase_harmonic_kernel hn, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_erase.mp hj
  have hnj : n ≠ j := Ne.symm hj'.1
  rw [← collarWeight_div_sqrt_mul (mem_Icc.mp hn).1 (mem_Icc.mp hj'.2).1 hnj]
  field_simp [hsn]

/-- The sum of the two pole rows has its elementary exact action. -/
theorem sum_pole_outer_rows {n N : ℕ} (_hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) / Real.sqrt j) =
      Real.sqrt n * (harmonic N : ℝ) + (N : ℝ) / Real.sqrt n := by
  have hterm (j : ℕ) (hj : j ∈ Icc 1 N) :
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) / Real.sqrt j =
        Real.sqrt n * (1 / (j : ℝ)) + 1 / Real.sqrt n := by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    have hsj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hj0).ne'
    calc
      _ = Real.sqrt n / (Real.sqrt j * Real.sqrt j) +
          (Real.sqrt j / Real.sqrt j) / Real.sqrt n := by ring
      _ = _ := by
        rw [Real.mul_self_sqrt hj0.le, div_self hsj]
        ring
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, sum_const]
  have hH : (∑ j ∈ Icc 1 N, 1 / (j : ℝ)) = harmonic N := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hH]
  simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one_div]

/-- The restored center matrix acts on the pole as one plus a boundary remainder. -/
theorem sum_pole_minus_collar_div_sqrt {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N,
      ((Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) - collarWeight n j) /
        Real.sqrt j) =
      (N : ℝ) / Real.sqrt n + Real.sqrt n *
        ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
          3 / (4 * (n : ℝ))) := by
  simp only [sub_div, sum_sub_distrib]
  rw [sum_pole_outer_rows hn, sum_collarWeight_div_sqrt hn]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

