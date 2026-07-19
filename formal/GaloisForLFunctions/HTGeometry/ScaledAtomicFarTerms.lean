import GaloisForLFunctions.HTGeometry.ScaledAtomicMirrored

/-!
# The far terms of the scaled atomic Gram

An atom distinct from both evaluation nodes contributes a term whose two factors are each bounded
below by a real separation, since the real part of each factor is exactly the difference of the
atom and the node.

Such a term is therefore `O(y²)`, the fastest-decaying of the three kinds of off-diagonal atomic
contribution.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The distance from a real point to an upper node is at least the real separation. -/
theorem norm_sub_upperNode_ge (a b y : ℝ) : |b - a| ≤ ‖(b : ℂ) - upperNode a y‖ := by
  have hre : ((b : ℂ) - upperNode a y).re = b - a := by
    simp [Complex.sub_re]
  calc |b - a| = |((b : ℂ) - upperNode a y).re| := by rw [hre]
    _ ≤ _ := Complex.abs_re_le_norm _

/-- The same for the conjugate node, whose real part agrees. -/
theorem norm_sub_conj_upperNode_ge (a b y : ℝ) :
    |b - a| ≤ ‖(b : ℂ) - (starRingEnd ℂ) (upperNode a y)‖ := by
  have hre : ((b : ℂ) - (starRingEnd ℂ) (upperNode a y)).re = b - a := by
    rw [conj_upperNode]
    simp [Complex.sub_re]
  calc |b - a| = |((b : ℂ) - (starRingEnd ℂ) (upperNode a y)).re| := by rw [hre]
    _ ≤ _ := Complex.abs_re_le_norm _

/-- **A far atom contributes `O(y²)`.**  When the atom differs from both nodes, its scaled
contribution is bounded by the height squared over the product of the two separations. -/
theorem norm_scaled_atomic_far_le {a a' b : ℝ} (y : ℝ) (hba : b ≠ a) (hba' : b ≠ a') (c : ℂ) :
    ‖(y : ℂ) ^ 2 * (c / (((b : ℂ) - upperNode a y) *
        ((b : ℂ) - (starRingEnd ℂ) (upperNode a' y))))‖
      ≤ y ^ 2 * ‖c‖ / (|b - a| * |b - a'|) := by
  have h1 : (0 : ℝ) < |b - a| := abs_pos.2 (sub_ne_zero.2 hba)
  have h2 : (0 : ℝ) < |b - a'| := abs_pos.2 (sub_ne_zero.2 hba')
  have hprod : (0 : ℝ) < |b - a| * |b - a'| := by positivity
  have hden : |b - a| * |b - a'| ≤ ‖((b : ℂ) - upperNode a y) *
      ((b : ℂ) - (starRingEnd ℂ) (upperNode a' y))‖ := by
    rw [norm_mul]
    exact mul_le_mul (norm_sub_upperNode_ge a b y) (norm_sub_conj_upperNode_ge a' b y)
      (le_of_lt h2) (norm_nonneg _)
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnum : y ^ 2 * (‖c‖ / ‖((b : ℂ) - upperNode a y) *
      ((b : ℂ) - (starRingEnd ℂ) (upperNode a' y))‖)
      ≤ y ^ 2 * (‖c‖ / (|b - a| * |b - a'|)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_div_of_nonneg_left (norm_nonneg c) hprod hden
  rw [mul_div_assoc]
  exact hnum

end

end GaloisForLFunctions.HTGeometry
