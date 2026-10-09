import GaloisForLFunctions.RHTower.WeilLogShiftFiniteMatrixReceiver

/-!
# Exact recurrences for individual inverse columns

A single history impulse produces a coefficient column with a zero prefix,
a positive reciprocal-diagonal seed, and homogeneous triangular equations
at every later row. Its moment response is the same column times the full
paired kernel and the square-root normalization.
-/

open Filter Topology Real
open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- The centered coefficient response to one history coordinate. -/
def weilLogShiftRecoveryCoefficientColumn (k n : ℕ) : ℝ :=
  weilLogShiftRecoveryInverse (weilLogShiftRecoveryUnitHistory k) n -
    weilLogShiftRecoveryInverse (fun _ => 0) n

/-- A history impulse has no effect before its visible coefficient seed. -/
theorem weilLogShiftRecoveryCoefficientColumn_eq_zero (k n : ℕ) (hn : n < k + 2) :
    weilLogShiftRecoveryCoefficientColumn k n = 0 := by
  apply sub_eq_zero.mpr
  apply weilLogShiftRecoveryInverse_prefix _ _ k _ n hn
  intro j hj
  rw [weilLogShiftRecoveryUnitHistory_apply, if_neg (by omega)]

/-- Every recovery row evaluates a coefficient column to its exact impulse. -/
theorem weilLogShiftRecoveryCoefficientColumn_row (k n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.Icc 2 n,
      weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight n j) =
        if n = k + 2 then 1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  have h := weilLogShiftRecoveryProbe_sub
    (weilLogShiftRecoveryInverse (weilLogShiftRecoveryUnitHistory k))
    (weilLogShiftRecoveryInverse (fun _ => 0)) (m + 2)
  change weilLogShiftRecoveryHistory
      (weilLogShiftRecoveryInverse (weilLogShiftRecoveryUnitHistory k)) m -
      weilLogShiftRecoveryHistory (weilLogShiftRecoveryInverse (fun _ => 0)) m = _ at h
  rw [weilLogShiftRecoveryHistory_inverse, weilLogShiftRecoveryHistory_inverse,
    weilLogShiftRecoveryUnitHistory_apply, sub_zero] at h
  simpa only [weilLogShiftRecoveryCoefficientColumn, Nat.add_right_cancel_iff] using h.symm

/-- The seed coefficient is exactly the reciprocal positive recovery diagonal. -/
theorem weilLogShiftRecoveryCoefficientColumn_seed (k : ℕ) :
    weilLogShiftRecoveryCoefficientColumn k (k + 2) =
      1 / weilLogShiftRecoveryWeight (k + 2) (k + 2) := by
  have h := weilLogShiftRecoveryCoefficientColumn_row k (k + 2) (by omega)
  rw [if_pos rfl] at h
  have hs : (∑ j ∈ Finset.Icc 2 (k + 2),
      weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (k + 2) j) =
      weilLogShiftRecoveryCoefficientColumn k (k + 2) *
        weilLogShiftRecoveryWeight (k + 2) (k + 2) := by
    apply Finset.sum_eq_single (k + 2)
    · intro j hj hne
      have hj' := Finset.mem_Icc.mp hj
      rw [weilLogShiftRecoveryCoefficientColumn_eq_zero k j (by omega), zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).elim
  rw [hs] at h
  exact (eq_div_iff (weilLogShiftRecoveryWeight_diagonal_pos (k + 2) (by omega)).ne').mpr h

theorem weilLogShiftRecoveryCoefficientColumn_seed_pos (k : ℕ) :
    0 < weilLogShiftRecoveryCoefficientColumn k (k + 2) := by
  rw [weilLogShiftRecoveryCoefficientColumn_seed]
  exact div_pos (by norm_num) (weilLogShiftRecoveryWeight_diagonal_pos (k + 2) (by omega))

/-- Past its seed, each column satisfies a homogeneous triangular equation. -/
theorem weilLogShiftRecoveryCoefficientColumn_row_zero (k n : ℕ) (hn : k + 2 < n) :
    (∑ j ∈ Finset.Icc 2 n,
      weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight n j) = 0 := by
  rw [weilLogShiftRecoveryCoefficientColumn_row k n (by omega), if_neg (by omega)]

/-- The weighted moment column is exactly the normalized coefficient column. -/
theorem weilLogShiftRecoveryMomentResponse_eq_coefficientColumn (y : ℝ) (k n : ℕ)
    (hn : 2 ≤ n) :
    weilLogShiftRecoveryMomentResponse y n k =
      (weilLogShiftRecoveryCoefficientColumn k n / sqrt n) * pairedLogKernel y n := by
  rw [weilLogShiftRecoveryMomentResponse, weilLogShiftRecoveryMomentCLM_apply]
  simp only [weilLogShiftRecoveryMoment, weilDeviation, if_pos hn,
    weilLogShiftRecoveryCoefficientColumn]
  ring

end RHTower
