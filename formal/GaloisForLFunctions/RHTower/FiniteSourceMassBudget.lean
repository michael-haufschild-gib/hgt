import GaloisForLFunctions.RHTower.FiniteSignedTriangleBound

/-!
# Finite interaction budgets with unequal physical masses

Each coupling is bounded by the sum of its two source masses. Summing these
budgets counts every mass exactly twice per vertex and leaves an explicit
diagonal reserve.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

theorem finiteSignedQuadratic_mass_gap {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (m : ι → ℝ) (C e : ℝ)
    (hm : ∀ i, 0 ≤ m i) (he : 0 ≤ e) (hd : ∀ i, C * m i ≤ M i i)
    (hoff : ∀ i j, i ≠ j → |M i j| ≤ e * (m i + m j)) :
    (C - 2 * Fintype.card ι * e) * (∑ i, m i) ≤ finiteSignedQuadratic M (fun _ => 1) := by
  classical
  have hb : (∑ i, ∑ j, |finiteSignedOffDiagonal M i j|) ≤
      (2 * Fintype.card ι * e) * (∑ i, m i) := by
    calc
      _ ≤ ∑ i, ∑ j, e * (m i + m j) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · simp only [finiteSignedOffDiagonal, if_pos hij, abs_zero]
          exact mul_nonneg he (add_nonneg (hm i) (hm j))
        · simpa only [finiteSignedOffDiagonal, if_neg hij] using hoff i j hij
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring
  have hdiag := Finset.sum_le_sum (s := Finset.univ) fun i _ => hd i
  rw [← Finset.mul_sum] at hdiag
  have hlo := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => neg_abs_le (finiteSignedOffDiagonal M i j)
  simp only [Finset.sum_neg_distrib] at hlo
  have hq := finiteSignedQuadratic_diagonal_off M (fun _ => 1)
  simp only [one_pow, mul_one] at hq
  nlinarith only [hb, hdiag, hlo, hq]

end RHTower
