import GaloisForLFunctions.HilbertMetric.Spectral.ClippedScalar
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity

/-!
# Two-sided spectral clipping

Projection onto `[-c,c]` preserves signs and discards exactly the excess
absolute value. Its discarded square is bounded by every higher integral
moment, the scalar estimate behind arXiv:2611.18829, equation (3.5).
-/

namespace GaloisForLFunctions.HilbertMetric.SymmetricClipping
noncomputable section
open scoped NNReal

/-- Nearest point in the symmetric interval of radius `c`. -/
def clip (c : ℝ≥0) (x : ℝ) : ℝ := max (-(c : ℝ)) (min x c)

theorem clip_bounds (c : ℝ≥0) (x : ℝ) : -(c : ℝ) ≤ clip c x ∧ clip c x ≤ c :=
  ⟨le_max_left _ _, max_le (by linarith only [c.coe_nonneg]) (min_le_right _ _)⟩

theorem clip_of_abs_le (c : ℝ≥0) {x : ℝ} (h : |x| ≤ c) : clip c x = x := by
  rw [clip, min_eq_left (abs_le.mp h).2, max_eq_right (abs_le.mp h).1]

theorem clip_of_le_neg (c : ℝ≥0) {x : ℝ} (h : x ≤ -(c : ℝ)) :
    clip c x = -(c : ℝ) := by
  exact max_eq_left ((min_le_left _ _).trans h)

theorem clip_of_ge (c : ℝ≥0) {x : ℝ} (h : (c : ℝ) ≤ x) : clip c x = c := by
  rw [clip, min_eq_right h, max_eq_right (by linarith only [c.coe_nonneg])]

/-- The clipping error is exactly the positive excess over the radius. -/
theorem abs_sub_clip (c : ℝ≥0) (x : ℝ) :
    |x - clip c x| = max (|x| - c) 0 := by
  rcases le_total x (-(c : ℝ)) with hx | hx
  · rw [clip_of_le_neg c hx, abs_of_nonpos (by linarith only [hx]),
      abs_of_nonpos (by linarith only [hx, c.coe_nonneg]),
      max_eq_left (by linarith only [hx])]
    ring
  · rcases le_total x (c : ℝ) with hx' | hx'
    · have h := abs_le.mpr ⟨hx, hx'⟩
      rw [clip_of_abs_le c h, sub_self, abs_zero, max_eq_right (sub_nonpos.mpr h)]
    · rw [clip_of_ge c hx', abs_of_nonneg (sub_nonneg.mpr hx'),
        abs_of_nonneg (c.coe_nonneg.trans hx'), max_eq_left (sub_nonneg.mpr hx')]

/-- Variational characterization of interval projection. -/
theorem clip_variational (c : ℝ≥0) (x : ℝ) {y : ℝ} (hy : |y| ≤ c) :
    (x - clip c x) * (y - clip c x) ≤ 0 := by
  rcases le_total x (-(c : ℝ)) with hx | hx
  · rw [clip_of_le_neg c hx]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
      (sub_nonneg.mpr (abs_le.mp hy).1)
  · rcases le_total x (c : ℝ) with hx' | hx'
    · rw [clip_of_abs_le c (abs_le.mpr ⟨hx, hx'⟩), sub_self, zero_mul]
    · rw [clip_of_ge c hx']
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx')
        (sub_nonpos.mpr (abs_le.mp hy).2)

/-- Any competing bounded scalar pays the clipping error and its distance to the clip. -/
theorem clip_pythagorean (c : ℝ≥0) (x : ℝ) {y : ℝ} (hy : |y| ≤ c) :
    (x - clip c x) ^ 2 + (y - clip c x) ^ 2 ≤ (x - y) ^ 2 := by
  nlinarith only [clip_variational c x hy]

/-- Clipping is firmly nonexpansive, stronger than ordinary Lipschitz continuity. -/
theorem clip_firm (c : ℝ≥0) (x y : ℝ) :
    (clip c x - clip c y) ^ 2 ≤ (clip c x - clip c y) * (x - y) := by
  have hx := clip_variational c x (abs_le.mpr (clip_bounds c y))
  have hy := clip_variational c y (abs_le.mpr (clip_bounds c x))
  nlinarith only [hx, hy]

/-- An integral-moment tail bound valid even at zero cutoff. -/
theorem clip_error_moment (c : ℝ≥0) (x : ℝ) (n : ℕ) :
    (c : ℝ) ^ n * (x - clip c x) ^ 2 ≤ |x| ^ (n + 2) := by
  rw [← sq_abs (x - clip c x), abs_sub_clip]
  rcases le_total |x| (c : ℝ) with h | h
  · rw [max_eq_right (sub_nonpos.mpr h)]
    simpa only [zero_pow (by omega : 2 ≠ 0), mul_zero] using
      pow_nonneg (abs_nonneg x) (n + 2)
  · rw [max_eq_left (sub_nonneg.mpr h), pow_add]
    apply mul_le_mul (pow_le_pow_left₀ c.coe_nonneg h n)
    · exact (sq_le_sq₀ (sub_nonneg.mpr h) (abs_nonneg x)).mpr
        (sub_le_self _ c.coe_nonneg)
    · exact sq_nonneg _
    · exact pow_nonneg (abs_nonneg x) n

end
end GaloisForLFunctions.HilbertMetric.SymmetricClipping
