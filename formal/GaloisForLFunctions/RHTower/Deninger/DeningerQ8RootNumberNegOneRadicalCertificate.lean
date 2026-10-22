import Mathlib.Tactic

/-!
# Radical certificate for the literature Q8 root-number-minus-one field

The explicit source witness is not the older `2, 3` radical candidate.  Example
1.3(ii) of Shankar--Södergren--Templier, *Sato--Tate equidistribution of certain
families of Artin L-functions*, identifies

`ℚ(√((5 + √5) * (41 + 6 * √41)))`

as a quaternionic degree-eight extension with the unique two-dimensional Artin
representation of root number `-1`.  This module formalizes the exact integral
eliminant of that radical, without asserting the external Galois-group or
epsilon-factor calculations.  Those remain the next arithmetic proof gates.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- Degree-eight eliminant of the radical in the documented root-number-minus-one
quaternion-field witness. -/
def deningerQ8RootNumberNegOneRadicalPolynomial : Polynomial ℤ :=
  X ^ (8 : ℕ) - C 820 * X ^ (6 : ℕ) + C 146780 * X ^ (4 : ℕ) - C 3362000 * X ^ (2 : ℕ) + C 16810000

/-- Exact radical certificate for the documented root-number-minus-one witness.
The theorem holds in every commutative ring and therefore has no hidden numerical
root calculation. -/
theorem deningerQ8_rootNumberNegOneRadicalPolynomial_eq_zero
    {R : Type*} [CommRing R] (x y z : R)
    (hx : x ^ (2 : ℕ) = 5) (hy : y ^ (2 : ℕ) = 41)
    (hz : z ^ (2 : ℕ) = (5 + x) * (41 + 6 * y)) :
    z ^ (8 : ℕ) - 820 * z ^ (6 : ℕ) + 146780 * z ^ (4 : ℕ) - 3362000 * z ^ (2 : ℕ) + 16810000 = 0 := by
  let r : R := 5 + x
  let u : R := z ^ (2 : ℕ)
  have hr : r ^ (2 : ℕ) - 10 * r + 20 = 0 := by
    calc
      r ^ (2 : ℕ) - 10 * r + 20 = x ^ (2 : ℕ) - 5 := by dsimp [r]; ring
      _ = 0 := by rw [hx]; norm_num
  have hu : u = r * (41 + 6 * y) := by
    simpa only [u, r] using hz
  have hquad : u ^ (2 : ℕ) - 82 * r * u + 205 * r ^ (2 : ℕ) = 0 := by
    rw [hu]
    calc
      (r * (41 + 6 * y)) ^ (2 : ℕ) - 82 * r * (r * (41 + 6 * y)) + 205 * r ^ (2 : ℕ) =
          r ^ (2 : ℕ) * ((41 + 6 * y) ^ (2 : ℕ) - 82 * (41 + 6 * y) + 205) := by ring
      _ = 0 := by
        rw [show (41 + 6 * y) ^ (2 : ℕ) - 82 * (41 + 6 * y) + 205 = 36 * (y ^ (2 : ℕ) - 41) by ring,
          hy]
        ring
  have hlinear : u ^ (2 : ℕ) - 82 * r * u + 2050 * r - 4100 = 0 := by
    calc
      u ^ (2 : ℕ) - 82 * r * u + 2050 * r - 4100 =
          (u ^ (2 : ℕ) - 82 * r * u + 205 * r ^ (2 : ℕ)) - 205 * (r ^ (2 : ℕ) - 10 * r + 20) := by ring
      _ = 0 := by rw [hquad, hr]; ring
  have hmul : r * (2050 - 82 * u) = 4100 - u ^ (2 : ℕ) := by
    linear_combination hlinear
  have helim : u ^ (4 : ℕ) - 820 * u ^ (3 : ℕ) + 146780 * u ^ (2 : ℕ) - 3362000 * u + 16810000 = 0 := by
    calc
      u ^ (4 : ℕ) - 820 * u ^ (3 : ℕ) + 146780 * u ^ (2 : ℕ) - 3362000 * u + 16810000 =
          (4100 - u ^ (2 : ℕ)) ^ (2 : ℕ) - 10 * (2050 - 82 * u) * (4100 - u ^ (2 : ℕ)) +
            20 * (2050 - 82 * u) ^ (2 : ℕ) := by ring
      _ = (r * (2050 - 82 * u)) ^ (2 : ℕ) - 10 * (2050 - 82 * u) *
            (r * (2050 - 82 * u)) + 20 * (2050 - 82 * u) ^ (2 : ℕ) := by rw [hmul]
      _ = (2050 - 82 * u) ^ (2 : ℕ) * (r ^ (2 : ℕ) - 10 * r + 20) := by ring
      _ = 0 := by rw [hr, mul_zero]
  dsimp [u] at helim
  simpa [← pow_mul] using helim

/-- Polynomial-evaluation form of the exact root-number-minus-one radical
certificate. -/
theorem deningerQ8RootNumberNegOneRadicalPolynomial_eval₂_eq_zero
    {R : Type*} [CommRing R] (x y z : R)
    (hx : x ^ (2 : ℕ) = 5) (hy : y ^ (2 : ℕ) = 41)
    (hz : z ^ (2 : ℕ) = (5 + x) * (41 + 6 * y)) :
    deningerQ8RootNumberNegOneRadicalPolynomial.eval₂ (Int.castRingHom R) z = 0 := by
  simpa [deningerQ8RootNumberNegOneRadicalPolynomial] using
    deningerQ8_rootNumberNegOneRadicalPolynomial_eq_zero x y z hx hy hz

end

end RHTower
