import Mathlib

/-!
# The place-marked Stokes polygon

In the group algebra of a commutative group, three marked faces telescope to zero whenever the two
composition relations `ab = c` and `cd = 1` hold.  Applied to the positive rational units this is
the positive place path of the six-clock and, with the exponents reversed, its reciprocal path.
Under the horizontal character each finite face evaluates to `1 - 6^{±x}`, so the two paths differ
by exactly the arch face `-(6^{x} - 6^{-x})`: the polygon identifies the required source object but
does not annihilate the arch face separately.

* `deningerPlaceTelescope` : **`(17)`/`(18)`: the marked telescope vanishes.**
* `deningerSixPositivePath`, `deningerSixReciprocalPath` : the two paths of the six-clock.
* `deningerHorizontalFinitePositive` : **`(20)`: each finite face is `1 - 6^{x}`.**
* `deningerHorizontalFace_difference` : **the paths differ by the arch face.**
-/

namespace GaloisForLFunctions

open MonoidAlgebra

/-- **The marked place telescope.**  Two composition relations make the three faces cancel. -/
theorem deningerPlaceTelescope {R : Type*} [CommRing R] {G : Type*} [CommGroup G]
    (a b c d : G) (hab : a * b = c) (hcd : c * d = 1) :
    (MonoidAlgebra.single a (1 : R) - 1)
        + MonoidAlgebra.single a (1 : R) * (MonoidAlgebra.single b (1 : R) - 1)
        + MonoidAlgebra.single c (1 : R) * (MonoidAlgebra.single d (1 : R) - 1) = 0 := by
  have hone : (MonoidAlgebra.single (1 : G) (1 : R)) = 1 := rfl
  rw [mul_sub, mul_sub, mul_one, mul_one, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, hab, hcd]
  simp only [one_mul]
  rw [hone]
  abel

/-- The positive place path of the six-clock, `(17)`, for the places `u₂` and `u₃`. -/
theorem deningerSixPositivePath {R : Type*} [CommRing R] {G : Type*} [CommGroup G]
    (u2 u3 : G) (m : ℤ) :
    (MonoidAlgebra.single ((u2 * u3) ^ m) (1 : R) - 1)
        + MonoidAlgebra.single ((u2 * u3) ^ m) (1 : R)
          * (MonoidAlgebra.single (u2 ^ (-m)) (1 : R) - 1)
        + MonoidAlgebra.single (u3 ^ m) (1 : R)
          * (MonoidAlgebra.single (u3 ^ (-m)) (1 : R) - 1) = 0 := by
  refine deningerPlaceTelescope _ _ _ _ ?_ ?_
  · rw [mul_zpow, mul_assoc, mul_comm (u3 ^ m), ← mul_assoc, ← zpow_add, add_neg_cancel,
      zpow_zero, one_mul]
  · rw [← zpow_add, add_neg_cancel, zpow_zero]

/-- The reciprocal place path of the six-clock, `(18)`. -/
theorem deningerSixReciprocalPath {R : Type*} [CommRing R] {G : Type*} [CommGroup G]
    (u2 u3 : G) (m : ℤ) :
    (MonoidAlgebra.single ((u2 * u3) ^ (-m)) (1 : R) - 1)
        + MonoidAlgebra.single ((u2 * u3) ^ (-m)) (1 : R)
          * (MonoidAlgebra.single (u2 ^ m) (1 : R) - 1)
        + MonoidAlgebra.single (u3 ^ (-m)) (1 : R)
          * (MonoidAlgebra.single (u3 ^ m) (1 : R) - 1) = 0 := by
  simpa using deningerSixPositivePath (R := R) u2 u3 (-m)

/-! ## The horizontal character -/

/-- **`(20)`: the positive finite face evaluates to `1 - 6^{x}`.** -/
theorem deningerHorizontalFinitePositive (x : ℝ) :
    (6 : ℝ) ^ x * ((2 : ℝ) ^ (-x) - 1) + (3 : ℝ) ^ x * ((3 : ℝ) ^ (-x) - 1)
      = 1 - (6 : ℝ) ^ x := by
  have h62 : (6 : ℝ) ^ x * (2 : ℝ) ^ (-x) = (3 : ℝ) ^ x := by
    have h6 : (6 : ℝ) = 3 * 2 := by norm_num
    rw [h6, Real.mul_rpow (by norm_num) (by norm_num), mul_assoc,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  have h33 : (3 : ℝ) ^ x * (3 : ℝ) ^ (-x) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  have hexpand : (6 : ℝ) ^ x * ((2 : ℝ) ^ (-x) - 1) + (3 : ℝ) ^ x * ((3 : ℝ) ^ (-x) - 1)
      = ((6 : ℝ) ^ x * (2 : ℝ) ^ (-x)) - (6 : ℝ) ^ x
        + ((3 : ℝ) ^ x * (3 : ℝ) ^ (-x)) - (3 : ℝ) ^ x := by ring
  rw [hexpand, h62, h33]
  ring

/-- The reciprocal finite face evaluates to `1 - 6^{-x}`. -/
theorem deningerHorizontalFiniteReciprocal (x : ℝ) :
    (6 : ℝ) ^ (-x) * ((2 : ℝ) ^ x - 1) + (3 : ℝ) ^ (-x) * ((3 : ℝ) ^ x - 1)
      = 1 - (6 : ℝ) ^ (-x) := by
  simpa using deningerHorizontalFinitePositive (-x)

/-- **The two paths differ by exactly the arch face.** -/
theorem deningerHorizontalFace_difference (x : ℝ) :
    ((6 : ℝ) ^ x * ((2 : ℝ) ^ (-x) - 1) + (3 : ℝ) ^ x * ((3 : ℝ) ^ (-x) - 1))
        - ((6 : ℝ) ^ (-x) * ((2 : ℝ) ^ x - 1) + (3 : ℝ) ^ (-x) * ((3 : ℝ) ^ x - 1))
      = -((6 : ℝ) ^ x - (6 : ℝ) ^ (-x)) := by
  rw [deningerHorizontalFinitePositive, deningerHorizontalFiniteReciprocal]
  ring

end GaloisForLFunctions
