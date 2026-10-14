import GaloisForLFunctions.HTGeometry.LpDiagonalSchattenEnergy
import GaloisForLFunctions.RHTower.SchattenLogResidueFiniteRankPerturbation
import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator

/-! # Finite-coordinate comparison for diagonal Schatten energy

Compression bounds coordinate energy by singular-value energy. For orders at
most one, the reverse bound costs only the number of retained coordinates
times the corresponding power of the discarded operator norm.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open RHTower ContinuousLinearMap

theorem schattenPowerPartialSum_diagonal_trunc (a : ℕ → ℂ)
    {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) {p : ℝ} (hp : 0 < p) (N : ℕ) :
    schattenPowerPartialSum p
      (diagonalOperator (truncMultiplier a N) (norm_truncMultiplier_le ha N)) N =
        ∑ n ∈ Finset.range N, ‖a n‖ ^ p := by
  let F := diagonalOperator (truncMultiplier a N) (norm_truncMultiplier_le ha N)
  have hC : 0 ≤ C := (norm_nonneg (a 0)).trans (ha 0)
  have he : F = lpDiagonalCLM (truncMultiplier a N) hC (norm_truncMultiplier_le ha N) := by
    ext x n
    rfl
  have hz (n : ℕ) (hn : n ∉ Finset.range N) : approxNumber F n = 0 := by
    apply le_antisymm
    · calc
        approxNumber F n ≤ approxNumber F N := approxNumber_antitone F (by simpa using hn)
        _ = 0 := approxNumber_eq_zero_of_hasRankLE (hasRankLE_diagonalOperator_trunc a ha N)
    · exact approxNumber_nonneg F n
  calc
    _ = ∑' n, approxNumber F n ^ p := by
      exact (tsum_eq_sum (s := Finset.range N) fun n hn => by rw [hz n hn, Real.zero_rpow hp.ne']).symm
    _ = ∑' n, ‖truncMultiplier a N n‖ ^ p := by
      rw [he, tsum_rpow_approxNumber_lpDiagonalCLM _ _ _ hp]
    _ = ∑ n ∈ Finset.range N, ‖truncMultiplier a N n‖ ^ p :=
      tsum_eq_sum fun n hn => by
        simp only [Finset.mem_range, not_lt] at hn
        simp [truncMultiplier, not_lt.mpr hn, Real.zero_rpow hp.ne']
    _ = _ := Finset.sum_congr rfl fun n hn => by simp [truncMultiplier, Finset.mem_range.mp hn]

theorem approxNumber_diagonal_trunc_le (a : ℕ → ℂ)
    {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) (N n : ℕ) :
    approxNumber (diagonalOperator (truncMultiplier a N) (norm_truncMultiplier_le ha N)) n ≤
      approxNumber (diagonalOperator a ha) n := by
  let b : ℕ → ℂ := fun k => if k < N then 1 else 0
  have hb (k : ℕ) : ‖b k‖ ≤ 1 := by simp [b]; split_ifs <;> norm_num
  have he : diagonalOperator (truncMultiplier a N) (norm_truncMultiplier_le ha N) =
      diagonalOperator b hb ∘L diagonalOperator a ha := by
    ext x k
    simp only [diagonalOperator_apply, comp_apply, truncMultiplier, b]
    split_ifs <;> simp
  rw [he]
  exact (approxNumber_comp_le_left _ _ n).trans
    (by simpa using (mul_le_mul_of_nonneg_right (norm_diagonalOperator_le b hb)
      (approxNumber_nonneg (diagonalOperator a ha) n)))

theorem diagonal_coordinate_energy_le (a : ℕ → ℂ)
    {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) {p : ℝ} (hp : 0 < p) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖a n‖ ^ p) ≤
      schattenPowerPartialSum p (diagonalOperator a ha) N := by
  rw [← schattenPowerPartialSum_diagonal_trunc a ha hp N]
  exact Finset.sum_le_sum fun n _ => Real.rpow_le_rpow (approxNumber_nonneg _ _)
    (approxNumber_diagonal_trunc_le a ha N n) hp.le

theorem diagonal_partial_energy_le_coordinate_add_tail (a : ℕ → ℂ)
    {C : ℝ} (ha : ∀ n, ‖a n‖ ≤ C) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (N : ℕ) :
    schattenPowerPartialSum p (diagonalOperator a ha) N ≤
      (∑ n ∈ Finset.range N, ‖a n‖ ^ p) + N *
        ‖diagonalOperator a ha -
          diagonalOperator (truncMultiplier a N) (norm_truncMultiplier_le ha N)‖ ^ p := by
  let T := diagonalOperator a ha
  let F := diagonalOperator (truncMultiplier a N) (norm_truncMultiplier_le ha N)
  have h (n : ℕ) : approxNumber T n ^ p ≤ approxNumber F n ^ p + ‖T - F‖ ^ p := by
    have hn := RHTower.approxNumber_add_le (T - F) F 0 n
    rw [zero_add, sub_add_cancel, approxNumber_zero_eq_norm] at hn
    calc
      _ ≤ (‖T - F‖ + approxNumber F n) ^ p :=
        Real.rpow_le_rpow (approxNumber_nonneg _ _) hn hp.le
      _ ≤ ‖T - F‖ ^ p + approxNumber F n ^ p :=
        Real.rpow_add_le_add_rpow (norm_nonneg _) (approxNumber_nonneg _ _) hp.le hp1
      _ = _ := add_comm _ _
  calc
    _ ≤ ∑ n ∈ Finset.range N, (approxNumber F n ^ p + ‖T - F‖ ^ p) :=
      Finset.sum_le_sum fun n _ => h n
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← schattenPowerPartialSum_diagonal_trunc a ha hp N]
      rfl

end
end GaloisForLFunctions.HTGeometry
