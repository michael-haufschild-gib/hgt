import GaloisForLFunctions.RHTower.WeilLogShiftLogGapIndexBounds
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeMoments

/-! The first logarithmic transport deficit is squeezed by the edge barycenter. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilCanonicalEdgeIndexMean_bounds (r k : ℕ) :
    0 ≤ finiteWeilCanonicalEdgeIndexMean r k ∧ finiteWeilCanonicalEdgeIndexMean r k ≤ (r : ℝ) := by
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (finiteWeilCanonicalEdgeMass_pos r k i).le (Nat.cast_nonneg _)
  · calc
      _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * (r : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (finiteWeilCanonicalEdgeMass_pos r k i).le
        exact_mod_cast (show (i : ℕ) ≤ r by have := i.isLt; omega)
      _ = _ := by rw [← Finset.sum_mul, finiteWeilCanonicalEdgeMass_sum, one_mul]

theorem finiteWeilCanonicalLogTransportCost_deficit_average (r k : ℕ) (b : ℝ) :
    (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
      (b * (1 - ((k + 2 : ℕ) : ℝ) *
        (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc)))) =
      b * (1 - ((k + 2 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCost r k) := by
  calc
    _ = (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * b) -
        b * ((k + 2 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCost r k := by
      rw [finiteWeilCanonicalLogTransportCost, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [← Finset.sum_mul, finiteWeilCanonicalEdgeMass_sum]; ring

theorem finiteWeilCanonicalLogTransportCost_deficit_bounds (r k : ℕ) :
    finiteWeilCanonicalEdgeIndexMean r k ≤ ((k + r + 3 : ℕ) : ℝ) *
        (1 - ((k + 2 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCost r k) ∧
      ((k + 2 : ℕ) : ℝ) * (1 - ((k + 2 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCost r k) ≤
        finiteWeilCanonicalEdgeIndexMean r k + 1 := by
  constructor
  · rw [← finiteWeilCanonicalLogTransportCost_deficit_average]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (finiteWeilClusterLogNodes_adjacent_deficit_bounds r k i).1
      (finiteWeilCanonicalEdgeMass_pos r k i).le
  · calc
      _ = ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
          (((k + 2 : ℕ) : ℝ) * (1 - ((k + 2 : ℕ) : ℝ) *
            (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc))) :=
        (finiteWeilCanonicalLogTransportCost_deficit_average r k _).symm
      _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * (((i : ℕ) : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (finiteWeilClusterLogNodes_adjacent_deficit_bounds r k i).2
          (finiteWeilCanonicalEdgeMass_pos r k i).le
      _ = _ := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, finiteWeilCanonicalEdgeMass_sum,
          finiteWeilCanonicalEdgeIndexMean]

end RHTower
