import Mathlib

/-!
# Hermitian radial line for Deninger's Poisson--Hodge source

The complex line is represented by its real coordinate plane.  Squared
radius converts half-density scaling into ordinary dilation; the same
scaling gives the weight-one area law.  Quarter rotation on one-forms
squares to `-1`, commutes with scaling, and turns the alternating area
pairing into a positive sum of squares.

No zeta zero, positivity assumption, or Riemann hypothesis occurs.
-/

namespace RHTower

/-- Squared Hermitian radius on the real coordinate plane of a complex line. -/
def deningerHermitianLineRadius (z : ℝ × ℝ) : ℝ :=
  z.1 ^ (2 : ℕ) + z.2 ^ (2 : ℕ)

/-- Scalar half-density action on the Hermitian line. -/
def deningerHermitianLineScale (s : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (s * z.1, s * z.2)

/-- Oriented Kähler area pairing on the real coordinate plane. -/
def deningerHermitianLineArea (z w : ℝ × ℝ) : ℝ :=
  z.1 * w.2 - z.2 * w.1

/-- Degree-one Hodge star, represented by positive quarter rotation. -/
def deningerHermitianLineHodge (z : ℝ × ℝ) : ℝ × ℝ :=
  (-z.2, z.1)

/-- Squared radius scales by the square of the half-density. -/
theorem deningerHermitianLineRadius_scale (s : ℝ) (z : ℝ × ℝ) :
    deningerHermitianLineRadius (deningerHermitianLineScale s z) =
      s ^ (2 : ℕ) * deningerHermitianLineRadius z := by
  simp only [deningerHermitianLineRadius, deningerHermitianLineScale]
  ring

/-- The Kähler area has the same weight as squared radius. -/
theorem deningerHermitianLineArea_scale
    (s : ℝ) (z w : ℝ × ℝ) :
    deningerHermitianLineArea
        (deningerHermitianLineScale s z)
        (deningerHermitianLineScale s w) =
      s ^ (2 : ℕ) * deningerHermitianLineArea z w := by
  simp only [deningerHermitianLineArea, deningerHermitianLineScale]
  ring

/-- On degree one, Hodge star squares to minus the identity. -/
theorem deningerHermitianLineHodge_sq (z : ℝ × ℝ) :
    deningerHermitianLineHodge (deningerHermitianLineHodge z) =
      (-z.1, -z.2) := by
  simp [deningerHermitianLineHodge]

/-- Cup followed by Hodge star is exactly squared Hermitian radius. -/
theorem deningerHermitianLineArea_hodge_self (z : ℝ × ℝ) :
    deningerHermitianLineArea z (deningerHermitianLineHodge z) =
      deningerHermitianLineRadius z := by
  simp only [deningerHermitianLineArea, deningerHermitianLineHodge,
    deningerHermitianLineRadius]
  ring

/-- The source Hodge metric is strictly positive away from zero. -/
theorem deningerHermitianLineHodge_positive
    {z : ℝ × ℝ} (hz : z ≠ (0, 0)) :
    0 < deningerHermitianLineArea z (deningerHermitianLineHodge z) := by
  rw [deningerHermitianLineArea_hodge_self]
  rcases z with ⟨x, y⟩
  simp only [deningerHermitianLineRadius] at hz ⊢
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      exact hz (by simp [hx, hy])
    have hysq : 0 < y ^ (2 : ℕ) := sq_pos_of_ne_zero hy
    nlinarith [sq_nonneg x]
  · have hxsq : 0 < x ^ (2 : ℕ) := sq_pos_of_ne_zero hx
    nlinarith [sq_nonneg y]

/-- Hodge star commutes with every scalar half-density map. -/
theorem deningerHermitianLineHodge_scale
    (s : ℝ) (z : ℝ × ℝ) :
    deningerHermitianLineHodge (deningerHermitianLineScale s z) =
      deningerHermitianLineScale s (deningerHermitianLineHodge z) := by
  ext <;> simp [deningerHermitianLineHodge, deningerHermitianLineScale]

/--
If `s² = q`, pullback by half-density `s` is dilation by `q` on every
radial test function.
-/
theorem deningerHermitianLineRadialPullback_eq_dilation
    (f : ℝ → ℂ) (s q : ℝ) (hsq : s ^ (2 : ℕ) = q) (z : ℝ × ℝ) :
    f (deningerHermitianLineRadius (deningerHermitianLineScale s z)) =
      f (q * deningerHermitianLineRadius z) := by
  rw [deningerHermitianLineRadius_scale, hsq]

end RHTower
