import GaloisForLFunctions.RHTower.WeilLogShiftLateColumnRunaway

/-!
# Exact alternating signs of late inverse columns

The native older tail costs at most half the adjacent term. The homogeneous
row equation therefore reverses the coefficient sign at every step after a
sufficiently late seed. The positive seed fixes the exact parity law.
-/

noncomputable section

namespace RHTower

private theorem opposite_sign_of_half_tail (u v d w R : ℝ)
    (hu : 0 < |u|) (hd : 0 < d) (hw : 0 < w)
    (hR : |R| ≤ w * |u| / 2) (heq : (R + u * w) + v * d = 0) : u * v < 0 := by
  obtain ⟨hRl, hRu⟩ := abs_le.mp hR
  rcases lt_or_gt_of_ne (abs_pos.mp hu) with hneg | hpos
  · rw [abs_of_neg hneg] at hRu
    have hprod : u * w < 0 := mul_neg_of_neg_of_pos hneg hw
    have hv : 0 < v := by
      by_contra hv
      have hmul : v * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hv) hd.le
      nlinarith only [heq, hRu, hprod, hmul]
    exact mul_neg_of_neg_of_pos hneg hv
  · rw [abs_of_pos hpos] at hRl
    have hprod : 0 < u * w := mul_pos hpos hw
    have hv : v < 0 := by
      by_contra hv
      have hmul : 0 ≤ v * d := mul_nonneg (le_of_not_gt hv) hd.le
      nlinarith only [heq, hRl, hprod, hmul]
    exact mul_neg_of_pos_of_neg hpos hv

/-- Every adjacent pair after any sufficiently late seed has opposite signs.
The common threshold is independent of the column and row. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_sign_reversal :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ n : ℕ, k + 2 ≤ n →
      weilLogShiftRecoveryCoefficientColumn k n *
        weilLogShiftRecoveryCoefficientColumn k (n + 1) < 0 := by
  obtain ⟨K, hK, hhalf⟩ := exists_weilLogShiftRecoveryCoefficientColumn_older_tail_half_bound
  refine ⟨K, hK, ?_⟩
  intro k hk n hn
  obtain ⟨hadj, hnonzero, hsum⟩ := hhalf k hk n hn
  have hdiag := weilLogShiftRecoveryWeight_diagonal_pos (n + 1) (by omega)
  have hrec := weilLogShiftRecoveryCoefficientColumn_row_zero k (n + 1) (by omega)
  rw [Finset.sum_Icc_succ_top (by omega)] at hrec
  have hsplit : (∑ j ∈ Finset.Icc 2 n,
      weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j) =
      (∑ j ∈ Finset.Icc 2 (n - 1),
        weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j) +
      weilLogShiftRecoveryCoefficientColumn k n * weilLogShiftRecoveryWeight (n + 1) n := by
    have h := Finset.sum_Icc_succ_top (a := 2) (b := n - 1) (by omega)
      (fun j => weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j)
    simpa only [show n - 1 + 1 = n by omega] using h
  rw [hsplit] at hrec
  exact opposite_sign_of_half_tail _ _ _ _ _ hnonzero hdiag hadj hsum hrec

/-- The positive seed and forced sign reversal determine the exact parity
of every coefficient after every sufficiently late seed. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_alternating_sign :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ n : ℕ, k + 2 ≤ n →
      0 < (-1 : ℝ) ^ (n + k) * weilLogShiftRecoveryCoefficientColumn k n := by
  obtain ⟨K, hK, hflip⟩ := exists_weilLogShiftRecoveryCoefficientColumn_sign_reversal
  refine ⟨K, hK, ?_⟩
  intro k hk n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hp : (-1 : ℝ) ^ (k + 2 + k) = 1 := by
        rw [show k + 2 + k = 2 * (k + 1) by omega, pow_mul]
        norm_num
      rw [hp, one_mul]
      exact weilLogShiftRecoveryCoefficientColumn_seed_pos k
  | succ n hn ih =>
      let s := (-1 : ℝ) ^ (n + k)
      have hs : s * s = 1 := by
        dsimp only [s]
        rw [← mul_pow]
        norm_num
      change 0 < s * weilLogShiftRecoveryCoefficientColumn k n at ih
      have hprod : (s * weilLogShiftRecoveryCoefficientColumn k n) *
          (s * weilLogShiftRecoveryCoefficientColumn k (n + 1)) < 0 := by
        calc
          _ = (s * s) * (weilLogShiftRecoveryCoefficientColumn k n *
              weilLogShiftRecoveryCoefficientColumn k (n + 1)) := by ring
          _ = weilLogShiftRecoveryCoefficientColumn k n *
              weilLogShiftRecoveryCoefficientColumn k (n + 1) := by rw [hs, one_mul]
          _ < 0 := hflip k hk n hn
      have hnext : s * weilLogShiftRecoveryCoefficientColumn k (n + 1) < 0 := by
        by_contra hnext
        have hnonneg := mul_nonneg ih.le (le_of_not_gt hnext)
        linarith only [hprod, hnonneg]
      rw [show n + 1 + k = (n + k) + 1 by omega, pow_succ]
      change 0 < (s * -1) * weilLogShiftRecoveryCoefficientColumn k (n + 1)
      nlinarith only [hnext]

end RHTower
