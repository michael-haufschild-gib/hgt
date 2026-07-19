import GaloisForLFunctions.HTGeometry.AtomMassLimit

/-!
# The scaled kernel against the Herglotz tail weight

For an infinite Herglotz measure the constant dominant is unavailable, and the tail must be
controlled by the growth weight `(1 + t²)⁻¹` that the Herglotz condition integrates.

Far from the node the two are comparable: outside a fixed interval around the node, `1 + t²` is
bounded by a constant multiple of `(t - a)²`.  So the scaled kernel is bounded there by the height
squared times the Herglotz weight, and the tail contribution vanishes with the height.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The comparison constant between the Herglotz weight and the squared distance to the node. -/
def tailComparison (a R : ℝ) : ℝ := 1 / R ^ 2 + (1 + |a| / R) ^ 2

theorem tailComparison_pos {a R : ℝ} (hR : 0 < R) : 0 < tailComparison a R := by
  rw [tailComparison]
  positivity

/-- **The Herglotz weight is dominated by the squared distance off a fixed interval.**  Outside the
interval of radius `R` about the node, `1 + t²` is at most a constant multiple of `(t - a)²`. -/
theorem one_add_sq_le_tailComparison_mul {a t R : ℝ} (hR : 0 < R) (h : R ≤ |t - a|) :
    1 + t ^ 2 ≤ tailComparison a R * (t - a) ^ 2 := by
  have hs : (0 : ℝ) < |t - a| := lt_of_lt_of_le hR h
  have hsq : |t - a| ^ 2 = (t - a) ^ 2 := sq_abs _
  -- The node distance dominates one, after scaling by the radius.
  have h1 : (1 : ℝ) ≤ (t - a) ^ 2 / R ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    rw [← hsq]
    nlinarith [h, hR.le, hs.le]
  -- The point is within the node distance plus the node.
  have habs : |t| ≤ |t - a| + |a| := by
    simpa using abs_sub_le t a 0
  have h2 : t ^ 2 ≤ (|t - a| + |a|) ^ 2 := by
    have : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [abs_nonneg t, abs_nonneg (t - a), abs_nonneg a, habs]
  have h3 : (|t - a| + |a|) ^ 2 ≤ (1 + |a| / R) ^ 2 * (t - a) ^ 2 := by
    have hfac : |t - a| + |a| ≤ (1 + |a| / R) * |t - a| := by
      have : |a| ≤ (|a| / R) * |t - a| := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hR]
        nlinarith [abs_nonneg a, h, hR]
      nlinarith [this]
    have hnn : (0 : ℝ) ≤ |t - a| + |a| := by positivity
    have hmul : (|t - a| + |a|) ^ 2 ≤ ((1 + |a| / R) * |t - a|) ^ 2 := by
      apply pow_le_pow_left₀ hnn hfac
    calc (|t - a| + |a|) ^ 2 ≤ ((1 + |a| / R) * |t - a|) ^ 2 := hmul
      _ = (1 + |a| / R) ^ 2 * (t - a) ^ 2 := by rw [mul_pow, hsq]
  rw [tailComparison, add_mul]
  have hdiv : (t - a) ^ 2 / R ^ 2 = 1 / R ^ 2 * (t - a) ^ 2 := by ring
  nlinarith [h1, h2, h3, hdiv]

/-- **The scaled kernel is bounded by the Herglotz weight off a fixed interval.**  This is the tail
bound that replaces the constant dominant when the measure is infinite. -/
theorem atomKernel_le_tail_weight {a t R y : ℝ} (hR : 0 < R) (h : R ≤ |t - a|) :
    atomKernel a y t ≤ y ^ 2 * tailComparison a R / (1 + t ^ 2) := by
  have hta : t ≠ a := by
    intro hEq
    rw [hEq] at h
    simp at h
    linarith
  have hsq : (0 : ℝ) < (t - a) ^ 2 := by
    have : t - a ≠ 0 := sub_ne_zero.2 hta
    positivity
  have hcomp := one_add_sq_le_tailComparison_mul hR h
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  refine le_trans (atomKernel_le_sq_div a t hta) ?_
  rw [div_le_div_iff₀ hsq hpos]
  nlinarith [sq_nonneg y, hcomp, hsq, tailComparison_pos (a := a) hR]

end

end GaloisForLFunctions.HTGeometry
