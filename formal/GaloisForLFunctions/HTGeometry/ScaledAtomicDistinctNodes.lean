import GaloisForLFunctions.HTGeometry.ScaledAtomicCrossTerms

/-!
# The distinct-node cross term of the scaled atomic Gram

An atom seen from two different nodes contributes a factor `-i y` from its own node and a factor
`(a - b) + i y` from the other.  Their product has imaginary part `-y (a - b)`, so its modulus is at
least the height times the node separation.

Only one power of the height is gained, so this term is `O(y)` rather than `O(y²)`.  It still
vanishes, which is all the limit requires.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The distinct-node denominator.**  The two Cauchy factors at distinct nodes multiply to
`y² - i y (a - b)`. -/
theorem sub_mul_sub_conj_upperNode_distinct (a b y : ℝ) :
    ((a : ℂ) - upperNode a y) * ((a : ℂ) - (starRingEnd ℂ) (upperNode b y))
      = (y : ℂ) ^ (2 : ℕ) - Complex.I * (y : ℂ) * ((a : ℂ) - (b : ℂ)) := by
  rw [sub_upperNode_self, conj_upperNode]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- The distinct-node denominator has imaginary part the height times the separation. -/
theorem im_sub_mul_sub_conj_distinct (a b y : ℝ) :
    (((a : ℂ) - upperNode a y) *
      ((a : ℂ) - (starRingEnd ℂ) (upperNode b y))).im = -(y * (a - b)) := by
  have him2 : ((y : ℂ) ^ (2 : ℕ)).im = 0 := by
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_im _
  rw [sub_mul_sub_conj_upperNode_distinct]
  simp [him2]

/-- **The distinct-node denominator is bounded below by height times separation.** -/
theorem norm_sub_mul_sub_conj_distinct_ge (a b y : ℝ) :
    |y| * |a - b| ≤ ‖((a : ℂ) - upperNode a y) *
      ((a : ℂ) - (starRingEnd ℂ) (upperNode b y))‖ := by
  have him := im_sub_mul_sub_conj_distinct a b y
  have hle := Complex.abs_im_le_norm
    (((a : ℂ) - upperNode a y) * ((a : ℂ) - (starRingEnd ℂ) (upperNode b y)))
  rw [him] at hle
  calc |y| * |a - b| = |-(y * (a - b))| := by rw [abs_neg, abs_mul]
    _ ≤ _ := hle

/-- **The distinct-node cross term is `O(y)`.**  Scaled by the height squared, an atom's
contribution across two distinct nodes is bounded by the height times the coefficient over the node
separation. -/
theorem norm_scaled_atomic_distinct_le {a b : ℝ} {y : ℝ} (hy : y ≠ 0) (hab : a ≠ b) (c : ℂ) :
    ‖(y : ℂ) ^ (2 : ℕ) * (c / (((a : ℂ) - upperNode a y) *
        ((a : ℂ) - (starRingEnd ℂ) (upperNode b y))))‖
      ≤ |y| * ‖c‖ / |a - b| := by
  have hyabs : (0 : ℝ) < |y| := abs_pos.2 hy
  have hsep : (0 : ℝ) < |a - b| := abs_pos.2 (sub_ne_zero.2 hab)
  have hden := norm_sub_mul_sub_conj_distinct_ge a b y
  have hdenpos : (0 : ℝ) < |y| * |a - b| := by positivity
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hnum : |y| ^ (2 : ℕ) * (‖c‖ / ‖((a : ℂ) - upperNode a y) *
      ((a : ℂ) - (starRingEnd ℂ) (upperNode b y))‖)
      ≤ |y| ^ (2 : ℕ) * (‖c‖ / (|y| * |a - b|)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_div_of_nonneg_left (norm_nonneg c) hdenpos hden
  refine le_trans hnum (le_of_eq ?_)
  field_simp

end

end GaloisForLFunctions.HTGeometry
