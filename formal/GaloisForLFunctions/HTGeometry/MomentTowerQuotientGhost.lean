import Mathlib

/-!
# Pointwise quotient of positive moment towers creates a signed ghost

Pointwise products of positive moment towers remain positive: they are moments of the product
measure.  Pointwise quotients have no such closure law.  This module records the smallest exact
counterexample and the algebraic residue that explains it.

For the positive two-atom tower `m_x(n) = 1 + x^n`, scalar deconvolution by `m_y` gives

`(1 + X) / (1 + Y) = 1 + X - Y + Y(Y-X)/(1+Y)`.

When `0 < Y < X`, both displayed correction terms are negative.  At `x=1/2`, `y=1/3`, the shifted
`3 x 3` Hankel determinant is already negative.  Thus a scalar spectral quotient can create an
alternating ghost spectrum even when numerator and denominator are positive finite-atomic moment
towers.  The surviving positive operation is tensor multiplication, formalized by the four-atom
identity below.
-/

namespace GaloisForLFunctions

/-- The moment tower of the positive two-atom measure `delta_1 + delta_x`. -/
def twoAtomMomentTower (x : ℝ) (n : ℕ) : ℝ :=
  1 + x ^ n

/-- Scalar pointwise deconvolution of two positive two-atom moment towers. -/
noncomputable def twoAtomMomentQuotient (x y : ℝ) (n : ℕ) : ℝ :=
  twoAtomMomentTower x n / twoAtomMomentTower y n

/-- The leading `3 x 3` shifted Hankel determinant, written in its five-moment form. -/
def shiftedHankelDetThree (s : ℕ → ℝ) (N : ℕ) : ℝ :=
  s N * s (N + 2) * s (N + 4) +
    2 * s (N + 1) * s (N + 2) * s (N + 3) -
    s N * s (N + 3) ^ (2 : ℕ) -
    s (N + 4) * s (N + 1) ^ (2 : ℕ) -
    s (N + 2) ^ (3 : ℕ)

/-- Tensor multiplication of two two-atom towers is the positive four-atom tower. -/
theorem twoAtomMomentTower_mul (x y : ℝ) (n : ℕ) :
    twoAtomMomentTower x n * twoAtomMomentTower y n =
      1 + x ^ n + y ^ n + (x * y) ^ n := by
  simp only [twoAtomMomentTower, mul_pow]
  ring

/-- Exact signed-ghost decomposition created by scalar moment deconvolution. -/
theorem twoAtomMomentQuotient_eq_signedGhost (X Y : ℝ) (hY : 1 + Y ≠ 0) :
    (1 + X) / (1 + Y) =
      1 + X - Y + Y * (Y - X) / (1 + Y) := by
  field_simp
  ring

/-- The ghost remainder has a strict negative sign when the denominator scale lies below the
numerator scale. -/
theorem signedGhostRemainder_neg {X Y : ℝ} (hY : 0 < Y) (hYX : Y < X) :
    Y * (Y - X) / (1 + Y) < 0 := by
  have hsub : Y - X < 0 := sub_neg.mpr hYX
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hY hsub) (by linarith)

/-- Positive moment towers are not closed under pointwise quotient: already the quotient of the
two-atom towers at `x=1/2`, `y=1/3` has a negative shifted `3 x 3` Hankel determinant. -/
theorem twoAtomMomentQuotient_half_third_hankelDetThree_neg :
    shiftedHankelDetThree
      (twoAtomMomentQuotient (1 / 2 : ℝ) (1 / 3 : ℝ)) 1 < 0 := by
  norm_num [shiftedHankelDetThree, twoAtomMomentQuotient, twoAtomMomentTower]

end GaloisForLFunctions
