import GaloisForLFunctions.HTGeometry.NodeRange
import GaloisForLFunctions.HTGeometry.GaussTightness

/-!
# Decay of the node weights

The quadrature identity `∑_ξ λₙ(ξ) ξ² = s₂` has nonnegative terms, so each one is bounded by the
total: a node at distance `|ξ|` carries weight at most `s₂ / ξ²`.

This is the single-node form of the tail estimate behind tightness, and it says the Gauss measures
cannot place appreciable mass far from the origin no matter how the nodes spread.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A single node's weighted square is bounded by the second moment.** -/
theorem christoffel_mul_sq_le (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) {xi : ℝ}
    (hxi : xi ∈ gaussNodes s n) :
    christoffel s n xi * xi ^ 2 ≤ s 2 := by
  classical
  rw [← gaussSum_pow h n 2 (by omega)]
  refine Finset.single_le_sum (f := fun z => christoffel s n z * z ^ 2) ?_ hxi
  intro z _
  exact mul_nonneg (christoffel_pos h n z).le (sq_nonneg z)

/-- The weight at a node decays quadratically in its distance from the origin. -/
theorem christoffel_le_div_sq (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) {xi : ℝ}
    (hxi : xi ∈ gaussNodes s n) (hne : xi ≠ 0) :
    christoffel s n xi ≤ s 2 / xi ^ 2 := by
  have hsq : 0 < xi ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  rw [le_div_iff₀ hsq]
  exact christoffel_mul_sq_le h hn hxi

/-- The same bound for the limit Christoffel function at a node. -/
theorem christoffelLimit_mul_sq_le (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) {xi : ℝ}
    (hxi : xi ∈ gaussNodes s n) :
    christoffelLimit s xi * xi ^ 2 ≤ s 2 := by
  refine le_trans ?_ (christoffel_mul_sq_le h hn hxi)
  exact mul_le_mul_of_nonneg_right (christoffelLimit_le h n xi) (sq_nonneg xi)

end HTGeometry
