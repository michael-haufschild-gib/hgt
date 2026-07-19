import GaloisForLFunctions.HTGeometry.AtomicGramMatrix

/-!
# The mirrored distinct-node estimate

The off-diagonal atomic entries contain two terms in which the atom sits at one of the two nodes:
one where it is the left node and one where it is the right.  The existing distinct-node estimate
covers the first; this file covers the second.

The computation is the mirror image — the product is `y² + i y (b - a)` rather than
`y² - i y (a - b)` — and the modulus bound is the same, the height times the node separation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The mirrored distinct-node denominator.** -/
theorem sub_mul_sub_conj_upperNode_mirrored (a b y : ℝ) :
    ((b : ℂ) - upperNode a y) * ((b : ℂ) - (starRingEnd ℂ) (upperNode b y))
      = (y : ℂ) ^ 2 + Complex.I * (y : ℂ) * ((b : ℂ) - (a : ℂ)) := by
  rw [sub_conj_upperNode_self, upperNode]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- The mirrored denominator has imaginary part the height times the separation. -/
theorem im_sub_mul_sub_conj_mirrored (a b y : ℝ) :
    (((b : ℂ) - upperNode a y) *
      ((b : ℂ) - (starRingEnd ℂ) (upperNode b y))).im = y * (b - a) := by
  have him2 : ((y : ℂ) ^ 2).im = 0 := by
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_im _
  rw [sub_mul_sub_conj_upperNode_mirrored]
  simp [him2]

/-- **The mirrored denominator is bounded below by height times separation.** -/
theorem norm_sub_mul_sub_conj_mirrored_ge (a b y : ℝ) :
    |y| * |b - a| ≤ ‖((b : ℂ) - upperNode a y) *
      ((b : ℂ) - (starRingEnd ℂ) (upperNode b y))‖ := by
  have him := im_sub_mul_sub_conj_mirrored a b y
  have hle := Complex.abs_im_le_norm
    (((b : ℂ) - upperNode a y) * ((b : ℂ) - (starRingEnd ℂ) (upperNode b y)))
  rw [him] at hle
  calc |y| * |b - a| = |y * (b - a)| := (abs_mul _ _).symm
    _ ≤ _ := hle

/-- **The mirrored distinct-node cross term is `O(y)`.** -/
theorem norm_scaled_atomic_mirrored_le {a b : ℝ} {y : ℝ} (hy : y ≠ 0) (hab : b ≠ a) (c : ℂ) :
    ‖(y : ℂ) ^ 2 * (c / (((b : ℂ) - upperNode a y) *
        ((b : ℂ) - (starRingEnd ℂ) (upperNode b y))))‖
      ≤ |y| * ‖c‖ / |b - a| := by
  have hyabs : (0 : ℝ) < |y| := abs_pos.2 hy
  have hsep : (0 : ℝ) < |b - a| := abs_pos.2 (sub_ne_zero.2 hab)
  have hden := norm_sub_mul_sub_conj_mirrored_ge a b y
  have hdenpos : (0 : ℝ) < |y| * |b - a| := by positivity
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hnum : |y| ^ 2 * (‖c‖ / ‖((b : ℂ) - upperNode a y) *
      ((b : ℂ) - (starRingEnd ℂ) (upperNode b y))‖)
      ≤ |y| ^ 2 * (‖c‖ / (|y| * |b - a|)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_div_of_nonneg_left (norm_nonneg c) hdenpos hden
  refine le_trans hnum (le_of_eq ?_)
  field_simp

end

end GaloisForLFunctions.HTGeometry
