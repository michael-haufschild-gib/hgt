import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorFullLongMomentExpansion
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovSharpSummatory
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# Sharp full-long base moment for the critical detector

The base component of the differentiated long energy has the exact Selberg-diagonal main term.
The error is uniform once the smooth-AFE head lies beyond the mollifier length.
-/

open Finset

namespace RHTower

noncomputable section

/-- Sharp Selberg-diagonal approximation to the full long base moment. -/
theorem abs_levinsonCriticalDetectorFullLongBaseMoment_sub_diagonal_harmonic_le
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    |levinsonCriticalDetectorFullLongBaseMoment L M -
        Sieve.barbanVehovSelbergDiagonal M *
          (∑ k ∈ Finset.Ioc L (L * M), 1 / (k : ℝ))| ≤
      2 * ((M : ℝ) * Real.log M) ^ 2 / ((L + 1 : ℕ) : ℝ) := by
  have hLpos : 0 < L := lt_of_lt_of_le (Nat.zero_lt_of_lt hM) hML
  have hLmul : L < L * M := by
    nlinarith [Nat.mul_pos hLpos (Nat.zero_lt_of_lt hM)]
  rw [levinsonCriticalDetectorFullLongBaseMoment]
  exact Sieve.abs_sum_Ioc_barbanVehovCoeff_sq_div_sub_diagonal_le hM.le hML hLmul

/-- Fully explicit logarithmic main term for the full long base moment. -/
theorem abs_levinsonCriticalDetectorFullLongBaseMoment_sub_diagonal_mul_log_le
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    |levinsonCriticalDetectorFullLongBaseMoment L M -
        Sieve.barbanVehovSelbergDiagonal M * Real.log M| ≤
      2 * ((M : ℝ) * Real.log M) ^ 2 / ((L + 1 : ℕ) : ℝ) +
        |Sieve.barbanVehovSelbergDiagonal M| *
          (1 / ((L * M : ℕ) : ℝ) + 1 / (L : ℝ)) := by
  let H : ℝ := ∑ k ∈ Finset.Ioc L (L * M), 1 / (k : ℝ)
  let D : ℝ := Sieve.barbanVehovSelbergDiagonal M
  let E : ℝ := 2 * ((M : ℝ) * Real.log M) ^ 2 / ((L + 1 : ℕ) : ℝ)
  have hLpos : 0 < L := lt_of_lt_of_le (Nat.zero_lt_of_lt hM) hML
  have hLmul : L < L * M := by
    nlinarith [Nat.mul_pos hLpos (Nat.zero_lt_of_lt hM)]
  have hbase : |levinsonCriticalDetectorFullLongBaseMoment L M - D * H| ≤ E := by
    exact abs_levinsonCriticalDetectorFullLongBaseMoment_sub_diagonal_harmonic_le hM hML
  have hlogeq : Real.log ((L * M : ℕ) : ℝ) - Real.log L = Real.log M := by
    push_cast
    rw [Real.log_mul (by positivity : (L : ℝ) ≠ 0) (by positivity : (M : ℝ) ≠ 0)]
    ring
  have hharm := HTGeometry.abs_sum_Ioc_inv_sub_log_le hLpos hLmul.le
  have hharm' :
      |H - (Real.log ((L * M : ℕ) : ℝ) - Real.log L)| ≤
        1 / ((L * M : ℕ) : ℝ) + 1 / (L : ℝ) := by
    simpa only [H, one_div] using hharm
  rw [hlogeq] at hharm'
  calc
    |levinsonCriticalDetectorFullLongBaseMoment L M - D * Real.log M| =
        |(levinsonCriticalDetectorFullLongBaseMoment L M - D * H) +
          D * (H - Real.log M)| := by congr 1; ring
    _ ≤ |levinsonCriticalDetectorFullLongBaseMoment L M - D * H| +
        |D * (H - Real.log M)| := abs_add_le _ _
    _ ≤ E + |D| * (1 / ((L * M : ℕ) : ℝ) + 1 / (L : ℝ)) := by
      rw [abs_mul]
      exact add_le_add hbase (mul_le_mul_of_nonneg_left hharm' (abs_nonneg D))

end

end RHTower
