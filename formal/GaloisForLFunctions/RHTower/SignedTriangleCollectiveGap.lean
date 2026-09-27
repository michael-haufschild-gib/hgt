import GaloisForLFunctions.RHTower.CCMWeilFrustratedTriangle

/-!
# A sign-independent collective correction

Every real edge has a nonnegative penalty relative to its separate-edge bound.
Four gauge choices detect every frustrated triangle. Taking the maximum of the
four nonnegative weights gives an unconditional correction for arbitrary entries.
-/

noncomputable section

namespace RHTower

def signedEdgePenalty (p x y : ℝ) : ℝ := |p| * (x ^ 2 + y ^ 2) + 2 * p * x * y

theorem signedEdgePenalty_eq (p x y : ℝ) :
    signedEdgePenalty p x y = max p 0 * (x + y) ^ 2 + max (-p) 0 * (x - y) ^ 2 := by
  unfold signedEdgePenalty
  rcases le_total 0 p with hp | hp
  · rw [abs_of_nonneg hp, max_eq_left hp, max_eq_right (neg_nonpos.mpr hp)]
    ring
  · rw [abs_of_nonpos hp, max_eq_right hp, max_eq_left (neg_nonneg.mpr hp)]
    ring

theorem signedEdgePenalty_nonneg (p x y : ℝ) : 0 ≤ signedEdgePenalty p x y := by
  rw [signedEdgePenalty_eq]
  positivity

theorem signedEdgePenalty_pos_part (p x y : ℝ) :
    max p 0 * (x + y) ^ 2 ≤ signedEdgePenalty p x y := by
  rw [signedEdgePenalty_eq]
  exact le_add_of_nonneg_right (mul_nonneg (le_max_right _ _) (sq_nonneg _))

theorem signedEdgePenalty_neg_part (p x y : ℝ) :
    max (-p) 0 * (x - y) ^ 2 ≤ signedEdgePenalty p x y := by
  rw [signedEdgePenalty_eq]
  exact le_add_of_nonneg_left (mul_nonneg (le_max_right _ _) (sq_nonneg _))

def signedTriangleGain (p q r : ℝ) : ℝ :=
  max (min (max p 0) (min (max q 0) (max r 0)))
    (max (min (max (-p) 0) (min (max (-q) 0) (max r 0)))
      (max (min (max (-p) 0) (min (max q 0) (max (-r) 0)))
        (min (max p 0) (min (max (-q) 0) (max (-r) 0)))))

theorem signedTriangleGain_nonneg (p q r : ℝ) : 0 ≤ signedTriangleGain p q r := by
  unfold signedTriangleGain
  positivity

theorem signedTriangleGain_eq_zero_of_zero (p q r : ℝ)
    (h : p = 0 ∨ q = 0 ∨ r = 0) : signedTriangleGain p q r = 0 := by
  apply le_antisymm _ (signedTriangleGain_nonneg p q r)
  rcases h with rfl | rfl | rfl
  · simp only [signedTriangleGain, neg_zero, max_self]
    repeat' apply max_le
    all_goals exact min_le_left _ _
  · simp only [signedTriangleGain, neg_zero, max_self]
    repeat' apply max_le
    all_goals exact (min_le_right _ _).trans (min_le_left _ _)
  · simp only [signedTriangleGain, neg_zero, max_self]
    repeat' apply max_le
    all_goals exact (min_le_right _ _).trans (min_le_right _ _)

theorem signedTriangleGain_pos_of_neg_neg_pos {p q r : ℝ}
    (hp : p < 0) (hq : q < 0) (hr : 0 < r) : 0 < signedTriangleGain p q r := by
  have h : 0 < min (max (-p) 0) (min (max (-q) 0) (max r 0)) :=
    lt_min ((neg_pos.mpr hp).trans_le (le_max_left _ _))
      (lt_min ((neg_pos.mpr hq).trans_le (le_max_left _ _)) (hr.trans_le (le_max_left _ _)))
  exact h.trans_le ((le_max_left _ _).trans (le_max_right _ _))

/-- No sign or positivity premise is required. -/
theorem signedTriangleGain_lower (p q r x y z : ℝ) :
    signedTriangleGain p q r * (x ^ 2 + y ^ 2 + z ^ 2) ≤
      signedEdgePenalty p x y + signedEdgePenalty q x z + signedEdgePenalty r y z := by
  have hm : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  unfold signedTriangleGain
  simp only [max_mul_of_nonneg _ _ hm]
  apply max_le
  · have h := frustratedTriangle_weighted_gap (max p 0) (max q 0) (max r 0)
      x (-y) (-z) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    have h₁ := signedEdgePenalty_pos_part p x y
    have h₂ := signedEdgePenalty_pos_part q x z
    have h₃ := signedEdgePenalty_pos_part r y z
    nlinarith only [h, h₁, h₂, h₃]
  · apply max_le
    · have h := frustratedTriangle_weighted_gap (max (-p) 0) (max (-q) 0) (max r 0)
        x y z (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
      have h₁ := signedEdgePenalty_neg_part p x y
      have h₂ := signedEdgePenalty_neg_part q x z
      have h₃ := signedEdgePenalty_pos_part r y z
      linarith only [h, h₁, h₂, h₃]
    · apply max_le
      · have h := frustratedTriangle_weighted_gap (max (-p) 0) (max q 0) (max (-r) 0)
          x y (-z) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
        have h₁ := signedEdgePenalty_neg_part p x y
        have h₂ := signedEdgePenalty_pos_part q x z
        have h₃ := signedEdgePenalty_neg_part r y z
        nlinarith only [h, h₁, h₂, h₃]
      · have h := frustratedTriangle_weighted_gap (max p 0) (max (-q) 0) (max (-r) 0)
          x (-y) z (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
        have h₁ := signedEdgePenalty_pos_part p x y
        have h₂ := signedEdgePenalty_neg_part q x z
        have h₃ := signedEdgePenalty_neg_part r y z
        nlinarith only [h, h₁, h₂, h₃]

end RHTower
