import GaloisForLFunctions.RHTower.WeilLagFunctionInteger

/-!
# Discrete arithmetic curvature of the integer Weil lag

Removing the logarithmic and trivial-zero terms from the scaled integer lag
leaves a sequence whose second difference is exactly `Λ(n)/n`. Thus three
consecutive corrected lag values recover one literal prime-power weight.
The uncorrected identity retains both archimedean second differences.
-/

open Real
open ArithmeticFunction (vonMangoldt)

namespace RHTower.IntegerLagCurvature

noncomputable section

/-- Scaled integer lag with its nonlinear archimedean terms removed. -/
def corrected (n : ℕ) : ℝ :=
  Real.sqrt n * integerLag n + n * Real.log n - trivialZeroSeriesReal n

private theorem corrected_eq (n : ℕ) :
    corrected (n + 2) =
      (n + 2 : ℕ) * (1 + eulerMascheroniConstant) - Real.log (2 * π) +
        (n + 2 : ℕ) * mertensSum (n + 2) - Chebyshev.psi (n + 2 : ℕ) := by
  rw [corrected, integerLag_eq (by omega : 2 ≤ n + 2)]
  have hs : Real.sqrt (n + 2 : ℕ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp
  ring

private theorem mertens_increment (n : ℕ) :
    mertensSum (n + 1) = mertensSum n + vonMangoldt (n + 1) / (n + 1 : ℕ) := by
  unfold mertensSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

private theorem psi_increment (n : ℕ) :
    Chebyshev.psi (n + 1 : ℕ) = Chebyshev.psi n + vonMangoldt (n + 1) := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc,
    Nat.floor_natCast, Nat.floor_natCast,
    Finset.sum_Icc_succ_top (by omega : 0 ≤ n + 1)]

/-- The first corrected lag difference is the complete Mertens sum plus its affine constant. -/
theorem corrected_first_difference (n : ℕ) :
    corrected (n + 3) - corrected (n + 2) =
      1 + eulerMascheroniConstant + mertensSum (n + 2) := by
  have hnext := corrected_eq (n + 1)
  have hbase := corrected_eq n
  rw [show n + 1 + 2 = n + 3 by omega] at hnext
  rw [hnext, hbase,
    show n + 3 = (n + 2) + 1 by omega,
    mertens_increment, psi_increment]
  push_cast
  field_simp
  ring

/-- Exact local recovery of the Mangoldt density from three corrected lag values. -/
theorem corrected_second_difference (n : ℕ) :
    corrected (n + 4) - 2 * corrected (n + 3) + corrected (n + 2) =
      vonMangoldt (n + 3) / (n + 3 : ℕ) := by
  have hnext := corrected_first_difference (n + 1)
  have hbase := corrected_first_difference n
  rw [show n + 1 + 3 = n + 4 by omega,
    show n + 1 + 2 = n + 3 by omega] at hnext
  have hm := mertens_increment (n + 2)
  rw [show n + 2 + 1 = n + 3 by omega] at hm
  linarith only [hnext, hbase, hm]

/-- Every corrected local curvature is nonnegative, without a zero-location assumption. -/
theorem corrected_second_difference_nonneg (n : ℕ) :
    0 ≤ corrected (n + 4) - 2 * corrected (n + 3) + corrected (n + 2) := by
  rw [corrected_second_difference]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- Strict corrected curvature detects exactly the prime powers. -/
theorem corrected_second_difference_pos_iff (n : ℕ) :
    0 < corrected (n + 4) - 2 * corrected (n + 3) + corrected (n + 2) ↔
      IsPrimePow (n + 3) := by
  rw [corrected_second_difference, div_pos_iff_of_pos_right (by positivity),
    ArithmeticFunction.vonMangoldt_pos_iff]

/-- Affine corrected triples occur exactly at indices which are not prime powers. -/
theorem corrected_second_difference_eq_zero_iff (n : ℕ) :
    corrected (n + 4) - 2 * corrected (n + 3) + corrected (n + 2) = 0 ↔
      ¬ IsPrimePow (n + 3) := by
  rw [corrected_second_difference, div_eq_zero_iff]
  simp only [show ((n + 3 : ℕ) : ℝ) ≠ 0 by positivity, or_false,
    ArithmeticFunction.vonMangoldt_eq_zero_iff]

/-- Native scaled lag curvature, retaining the full logarithmic and trivial-zero corrections. -/
theorem scaled_second_difference (n : ℕ) :
    Real.sqrt (n + 4 : ℕ) * integerLag (n + 4) -
        2 * (Real.sqrt (n + 3 : ℕ) * integerLag (n + 3)) +
        Real.sqrt (n + 2 : ℕ) * integerLag (n + 2) =
      vonMangoldt (n + 3) / (n + 3 : ℕ) -
        ((n + 4 : ℕ) * Real.log (n + 4 : ℕ) -
          2 * ((n + 3 : ℕ) * Real.log (n + 3 : ℕ)) +
          (n + 2 : ℕ) * Real.log (n + 2 : ℕ)) +
        (trivialZeroSeriesReal (n + 4 : ℕ) -
          2 * trivialZeroSeriesReal (n + 3 : ℕ) + trivialZeroSeriesReal (n + 2 : ℕ)) := by
  have h := corrected_second_difference n
  unfold corrected at h
  linarith only [h]

end
end RHTower.IntegerLagCurvature
