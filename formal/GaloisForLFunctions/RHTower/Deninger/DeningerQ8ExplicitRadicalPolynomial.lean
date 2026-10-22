import Mathlib.Tactic

/-!
# Legacy radical polynomial certificate

This module records the elementary identity for
`z² = (2 + √2) (3 + √3)`.  It is **not** the literature witness used in
Deninger's root-number-minus-one argument: the documented `Q₈` witness is
handled separately in `DeningerQ8RootNumberNegOneRadicalCertificate.lean`.

The theorem below is retained as a standalone algebraic identity.  It does
not assert that its splitting field has Galois group `Q₈`, nor any Artin
root-number calculation.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- The quartic eliminant of the squared radical generator. -/
def deningerQ8RadicalEliminant : Polynomial ℤ :=
  X ^ (4 : ℕ) - C 24 * X ^ (3 : ℕ) + C 144 * X ^ (2 : ℕ) - C 288 * X + C 144

/-- The degree-eight polynomial of the explicit radical generator. -/
def deningerQ8RadicalPolynomial : Polynomial ℤ :=
  X ^ (8 : ℕ) - C 24 * X ^ (6 : ℕ) + C 144 * X ^ (4 : ℕ) - C 288 * X ^ (2 : ℕ) + C 144

/-- **Algebraic radical certificate.** In every commutative ring, elements
with squares `2`, `3`, and `(2+x)(3+y)` satisfy the standard degree-eight
quaternion-field eliminant. -/
theorem deningerQ8_explicitRadicalPolynomial_eq_zero
    {R : Type*} [CommRing R] (x y z : R)
    (hx : x ^ (2 : ℕ) = 2) (hy : y ^ (2 : ℕ) = 3)
    (hz : z ^ (2 : ℕ) = (2 + x) * (3 + y)) :
    z ^ (8 : ℕ) - 24 * z ^ (6 : ℕ) + 144 * z ^ (4 : ℕ) - 288 * z ^ (2 : ℕ) + 144 = 0 := by
  let r : R := 2 + x
  let u : R := z ^ (2 : ℕ)
  have hr : r ^ (2 : ℕ) - 4 * r + 2 = 0 := by
    calc
      r ^ (2 : ℕ) - 4 * r + 2 = x ^ (2 : ℕ) - 2 := by dsimp [r]; ring
      _ = 0 := by rw [hx]; norm_num
  have hu : u = r * (3 + y) := by
    simpa only [u, r] using hz
  have hquad : u ^ (2 : ℕ) - 6 * r * u + 6 * r ^ (2 : ℕ) = 0 := by
    rw [hu]
    calc
      (r * (3 + y)) ^ (2 : ℕ) - 6 * r * (r * (3 + y)) + 6 * r ^ (2 : ℕ) =
          r ^ (2 : ℕ) * ((3 + y) ^ (2 : ℕ) - 6 * (3 + y) + 6) := by ring
      _ = 0 := by
        rw [show (3 + y) ^ (2 : ℕ) - 6 * (3 + y) + 6 = y ^ (2 : ℕ) - 3 by ring, hy]
        ring
  have hlinear : u ^ (2 : ℕ) - 6 * r * u + 24 * r - 12 = 0 := by
    calc
      u ^ (2 : ℕ) - 6 * r * u + 24 * r - 12 =
          (u ^ (2 : ℕ) - 6 * r * u + 6 * r ^ (2 : ℕ)) - 6 * (r ^ (2 : ℕ) - 4 * r + 2) := by
            ring
      _ = 0 := by rw [hquad, hr]; ring
  have hmul : r * (24 - 6 * u) = 12 - u ^ (2 : ℕ) := by
    linear_combination hlinear
  have helim : u ^ (4 : ℕ) - 24 * u ^ (3 : ℕ) + 144 * u ^ (2 : ℕ) - 288 * u + 144 = 0 := by
    calc
      u ^ (4 : ℕ) - 24 * u ^ (3 : ℕ) + 144 * u ^ (2 : ℕ) - 288 * u + 144 =
          (12 - u ^ (2 : ℕ)) ^ (2 : ℕ) - 4 * (24 - 6 * u) * (12 - u ^ (2 : ℕ)) +
            2 * (24 - 6 * u) ^ (2 : ℕ) := by ring
      _ = (r * (24 - 6 * u)) ^ (2 : ℕ) - 4 * (24 - 6 * u) *
            (r * (24 - 6 * u)) + 2 * (24 - 6 * u) ^ (2 : ℕ) := by rw [hmul]
      _ = (24 - 6 * u) ^ (2 : ℕ) * (r ^ (2 : ℕ) - 4 * r + 2) := by ring
      _ = 0 := by rw [hr, mul_zero]
  dsimp [u] at helim
  simpa [← pow_mul] using helim

/-- Polynomial-evaluation form of the explicit radical certificate. -/
theorem deningerQ8RadicalPolynomial_eval₂_eq_zero
    {R : Type*} [CommRing R] (x y z : R)
    (hx : x ^ (2 : ℕ) = 2) (hy : y ^ (2 : ℕ) = 3)
    (hz : z ^ (2 : ℕ) = (2 + x) * (3 + y)) :
    deningerQ8RadicalPolynomial.eval₂ (Int.castRingHom R) z = 0 := by
  simpa [deningerQ8RadicalPolynomial] using
    deningerQ8_explicitRadicalPolynomial_eq_zero x y z hx hy hz

end

end RHTower
