import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact inverse of a large-value exponent envelope

Writing `x = βν` turns the large-value envelope of Definition 2.2 of
arXiv:2610.09567 into a minimum and maximum of affine functions. Reversing the
level inequalities gives its threshold cost exactly, as in equation (8.1).
No large-value estimate is assumed: these are identities of the exponent profiles.
-/

noncomputable section
namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

/-- The combined large-value exponent in the cost coordinate `x = βν`. -/
def largeValueCostEnvelope (β τ x : ℝ) : ℝ :=
  min τ (max (2 * x)
    (min (τ + 6 * x - 2 * β)
      (min (max (τ + 4 * x - 8 / 5 * β) (τ / 2 + 4 * x - β))
        (τ + 2 * x - β))))

/-- Exact least nonnegative cost at a level below the height cap. -/
def largeValueInverseProfile (β τ t : ℝ) : ℝ :=
  max 0 (min (t / 2)
    (max ((t - τ + 2 * β) / 6)
      (max (min ((t - τ + 8 / 5 * β) / 4) ((t - τ / 2 + β) / 4))
        ((t - τ + β) / 2))))

/-- Every inverse-profile value is a nonnegative cost. -/
theorem largeValueInverseProfile_nonneg (β τ t : ℝ) :
    0 ≤ largeValueInverseProfile β τ t := le_max_left _ _

/-- Level sets of the envelope are exactly rays starting at the inverse profile. -/
theorem largeValueCostEnvelope_level_iff (β τ t x : ℝ) :
    t ≤ largeValueCostEnvelope β τ |x| ↔
      t ≤ τ ∧ largeValueInverseProfile β τ t ≤ |x| := by
  have h₁ : t ≤ 2 * |x| ↔ t / 2 ≤ |x| := by constructor <;> intro h <;> linarith only [h]
  have h₂ : t ≤ τ + 6 * |x| - 2 * β ↔ (t - τ + 2 * β) / 6 ≤ |x| := by
    constructor <;> intro h <;> linarith only [h]
  have h₃ : t ≤ τ + 4 * |x| - 8 / 5 * β ↔ (t - τ + 8 / 5 * β) / 4 ≤ |x| := by
    constructor <;> intro h <;> linarith only [h]
  have h₄ : t ≤ τ / 2 + 4 * |x| - β ↔ (t - τ / 2 + β) / 4 ≤ |x| := by
    constructor <;> intro h <;> linarith only [h]
  have h₅ : t ≤ τ + 2 * |x| - β ↔ (t - τ + β) / 2 ≤ |x| := by
    constructor <;> intro h <;> linarith only [h]
  simp only [largeValueCostEnvelope, largeValueInverseProfile, le_min_iff, le_max_iff,
    max_le_iff, min_le_iff, abs_nonneg, true_and, h₁, h₂, h₃, h₄, h₅]

/-- Every attainable capped level has its least cost, not merely an unattained infimum. -/
theorem largeValueInverseProfile_isLeast (β τ t : ℝ) :
    IsLeast {x : ℝ | 0 ≤ x ∧ min t τ ≤ largeValueCostEnvelope β τ x}
      (largeValueInverseProfile β τ (min t τ)) := by
  have hp := largeValueInverseProfile_nonneg β τ (min t τ)
  constructor
  · refine ⟨hp, ?_⟩
    have h := (largeValueCostEnvelope_level_iff β τ (min t τ)
      (largeValueInverseProfile β τ (min t τ))).mpr ⟨min_le_right _ _, by rw [abs_of_nonneg hp]⟩
    simpa only [abs_of_nonneg hp] using h
  · intro x hx
    have h := (largeValueCostEnvelope_level_iff β τ (min t τ) x).mp
      (by simpa only [abs_of_nonneg hx.1] using hx.2)
    simpa only [abs_of_nonneg hx.1] using h.2

#print axioms largeValueCostEnvelope_level_iff
#print axioms largeValueInverseProfile_isLeast

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
