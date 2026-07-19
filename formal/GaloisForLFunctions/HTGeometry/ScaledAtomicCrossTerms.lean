import GaloisForLFunctions.HTGeometry.ScaledAtomicGram

/-!
# Decay of the cross terms of the scaled atomic Gram

Besides an atom's own contribution at the node above it, the scaled atomic Gram has two kinds of
cross term: a *different* atom seen from the same node, and the same atom seen from two *different*
nodes.

Both vanish with the height.  The first has a denominator bounded away from zero, so it is `O(y²)`.
The second has a denominator whose imaginary part is `y` times the node separation, so it is `O(y)`.
Together with the exact own-atom diagonal and the measure limit, this makes the scaled Gram matrix
converge to the diagonal of coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- For a real evaluation point the conjugate factor is the conjugate of the factor. -/
theorem sub_conj_upperNode_eq_conj (a b y : ℝ) :
    (b : ℂ) - (starRingEnd ℂ) (upperNode a y)
      = (starRingEnd ℂ) ((b : ℂ) - upperNode a y) := by
  rw [map_sub, Complex.conj_ofReal]

/-- **A different atom seen from the same node.**  The two factors multiply to the squared distance,
which is bounded below by the atom separation. -/
theorem sub_mul_sub_conj_upperNode_other (a b y : ℝ) :
    ((b : ℂ) - upperNode a y) * ((b : ℂ) - (starRingEnd ℂ) (upperNode a y))
      = ((((b - a) ^ 2 + y ^ 2 : ℝ)) : ℂ) := by
  rw [sub_conj_upperNode_eq_conj, Complex.mul_conj]
  norm_cast
  rw [← normSq_sub_upperNode a y b]

/-- The cross denominator is bounded below by the squared atom separation. -/
theorem norm_sub_mul_sub_conj_other_ge {a b : ℝ} (y : ℝ) (hab : b ≠ a) :
    (b - a) ^ 2 ≤ ‖((b : ℂ) - upperNode a y) *
      ((b : ℂ) - (starRingEnd ℂ) (upperNode a y))‖ := by
  rw [sub_mul_sub_conj_upperNode_other, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b - a) ^ 2 + y ^ 2)]
  nlinarith [sq_nonneg y]

/-- **The cross term from a different atom is `O(y²)`.**  Scaled by the height squared, the
contribution of an atom at `b` seen from the node above `a` is bounded by the height squared over the
squared separation. -/
theorem norm_scaled_atomic_cross_le {a b : ℝ} (y : ℝ) (hab : b ≠ a) (c : ℂ) :
    ‖(y : ℂ) ^ 2 * (c / (((b : ℂ) - upperNode a y) *
        ((b : ℂ) - (starRingEnd ℂ) (upperNode a y))))‖
      ≤ y ^ 2 * ‖c‖ / (b - a) ^ 2 := by
  have hsep : (0 : ℝ) < (b - a) ^ 2 := by
    have : b - a ≠ 0 := sub_ne_zero.2 hab
    positivity
  rw [sub_mul_sub_conj_upperNode_other, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b - a) ^ 2 + y ^ 2)]
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hle : ‖c‖ / ((b - a) ^ 2 + y ^ 2) ≤ ‖c‖ / (b - a) ^ 2 := by
    apply div_le_div_of_nonneg_left (norm_nonneg c) hsep
    nlinarith [sq_nonneg y]
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end GaloisForLFunctions.HTGeometry
