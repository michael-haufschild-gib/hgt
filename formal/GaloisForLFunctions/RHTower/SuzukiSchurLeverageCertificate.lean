import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Bounds.Basic

/-!
# The Schur leverage certificate

Three completions of squares carry the certificate.

The variational form of a positive quadratic is attained: the supremum of `2dv - S v²` over the free
direction is `d²/S`, reached at `v = d/S`.  Dually, the Tikhonov infimum of `1 - 2uc + (K+r)c²` is
`1 - u²/(K+r)`, which is the exact identification of the regularized approximation defect with the
resolvent defect.

The block splitting is the same completion carried out in two variables: for a positive definite
two-block form, the inverse quadratic form is the high-block resolvent mass plus the Schur leverage
of the corrected low-block vector.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The variational form of the leverage -/

/-- **`(376)`: the leverage is the attained supremum of the linear-minus-quadratic functional.** -/
theorem isGreatest_leverage {S d : ℝ} (hS : 0 < S) :
    IsGreatest {y : ℝ | ∃ v : ℝ, y = 2 * d * v - S * v ^ 2} (d ^ 2 / S) := by
  constructor
  · refine ⟨d / S, ?_⟩
    field_simp
    ring
  · rintro y ⟨v, rfl⟩
    rw [le_div_iff₀ hS]
    nlinarith [sq_nonneg (S * v - d)]

/-! ## The Tikhonov infimum -/

/-- **`(380)`: the regularized approximation defect is the resolvent defect.** -/
theorem isLeast_tikhonov {K r u : ℝ} (hKr : 0 < K + r) :
    IsLeast {y : ℝ | ∃ c : ℝ, y = 1 - 2 * u * c + (K + r) * c ^ 2} (1 - u ^ 2 / (K + r)) := by
  constructor
  · refine ⟨u / (K + r), ?_⟩
    field_simp
    ring
  · rintro y ⟨c, rfl⟩
    have hle : 2 * u * c - (K + r) * c ^ 2 ≤ u ^ 2 / (K + r) := by
      rw [le_div_iff₀ hKr]
      nlinarith [sq_nonneg ((K + r) * c - u)]
    linarith

/-! ## The block splitting -/

/-- **`(378)`: the inverse quadratic form of a positive definite two-block form splits into the
high-block resolvent mass and the Schur leverage of the corrected low vector.** -/
theorem schur_quadratic_split {L B D uL uH : ℝ} (hD : 0 < D) (hdet : 0 < L * D - B ^ 2) :
    (D * uL ^ 2 - 2 * B * uL * uH + L * uH ^ 2) / (L * D - B ^ 2)
      = uH ^ 2 / D + (uL - B * uH / D) ^ 2 / (L - B ^ 2 / D) := by
  have hsc : L - B ^ 2 / D = (L * D - B ^ 2) / D := by
    field_simp
  rw [hsc]
  have hDne : D ≠ 0 := ne_of_gt hD
  have hne : L * D - B ^ 2 ≠ 0 := ne_of_gt hdet
  have hne2 : D * L - B ^ 2 ≠ 0 := by
    intro h
    exact hne (by linarith)
  field_simp
  ring

/-- The Schur complement is positive whenever the block form is. -/
theorem schur_complement_pos {L B D : ℝ} (hD : 0 < D) (hdet : 0 < L * D - B ^ 2) :
    0 < L - B ^ 2 / D := by
  have h : L - B ^ 2 / D = (L * D - B ^ 2) / D := by field_simp
  rw [h]
  exact div_pos hdet hD

end GaloisForLFunctions.RHTower
