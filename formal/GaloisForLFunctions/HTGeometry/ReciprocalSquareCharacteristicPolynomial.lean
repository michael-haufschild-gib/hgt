import Mathlib

/-!
# Reciprocal squares share one nonzero characteristic polynomial

For a rectangular matrix `D`, the reciprocal squares `Dᴴ * D` and `D * Dᴴ` have one complete
nonzero characteristic factor. Their characteristic polynomials differ only by the power of `X`
forced by the dimension imbalance. This is the rectangular Sylvester `AB`--`BA` identity.

The theorem works over an arbitrary commutative star ring. It needs no positivity, field,
diagonalization, or analytic spectral theorem. The complex corollaries connect it to the
positive reciprocal squares used elsewhere in this project.

This algebraic bridge is standard. It does not identify either square with quantum, gauge,
causal, or gravitational physics.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped Matrix

/--
The domain reciprocal square has the codomain characteristic polynomial, with exactly the
dimension-forced zero factor.
-/
theorem reciprocalSquare_charpoly_eq_of_card_le
    {R m n : Type*} [CommRing R] [Star R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n R) (h : Fintype.card m ≤ Fintype.card n) :
    (Dᴴ * D).charpoly =
      X ^ (Fintype.card n - Fintype.card m) * (D * Dᴴ).charpoly :=
  Matrix.charpoly_mul_comm_of_le Dᴴ D h

/--
The codomain reciprocal square has the domain characteristic polynomial, with exactly the
dimension-forced zero factor.
-/
theorem reciprocalSquare_charpoly_eq_of_card_ge
    {R m n : Type*} [CommRing R] [Star R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n R) (h : Fintype.card n ≤ Fintype.card m) :
    (D * Dᴴ).charpoly =
      X ^ (Fintype.card m - Fintype.card n) * (Dᴴ * D).charpoly :=
  Matrix.charpoly_mul_comm_of_le D Dᴴ h

/-- Coefficients above the forced zero factor agree term by term. -/
theorem reciprocalSquare_charpoly_coeff_add_eq_of_card_le
    {R m n : Type*} [CommRing R] [Star R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n R) (h : Fintype.card m ≤ Fintype.card n) (k : ℕ) :
    (Dᴴ * D).charpoly.coeff
        ((Fintype.card n - Fintype.card m) + k) =
      (D * Dᴴ).charpoly.coeff k := by
  rw [reciprocalSquare_charpoly_eq_of_card_le D h]
  simpa only [Nat.add_comm] using
    Polynomial.coeff_X_pow_mul (D * Dᴴ).charpoly
      (Fintype.card n - Fintype.card m) k

/-- Every coefficient below the forced zero factor vanishes. -/
theorem reciprocalSquare_charpoly_coeff_eq_zero_of_lt_card_sub
    {R m n : Type*} [CommRing R] [Star R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n R) (h : Fintype.card m ≤ Fintype.card n)
    (k : ℕ) (hk : k < Fintype.card n - Fintype.card m) :
    (Dᴴ * D).charpoly.coeff k = 0 := by
  rw [reciprocalSquare_charpoly_eq_of_card_le D h,
    Polynomial.coeff_X_pow_mul']
  simp only [ite_eq_right_iff]
  exact fun hle => (Nat.not_le_of_gt hk hle).elim

/-- Equal finite dimensions remove the forced zero factor entirely. -/
theorem reciprocalSquare_charpoly_eq_of_card_eq
    {R m n : Type*} [CommRing R] [Star R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n R) (h : Fintype.card m = Fintype.card n) :
    (Dᴴ * D).charpoly = (D * Dᴴ).charpoly := by
  simpa [h] using reciprocalSquare_charpoly_eq_of_card_le D h.le

/--
Complex reciprocal-domain and reciprocal-codomain squares share one nonzero characteristic
polynomial.
-/
theorem complex_reciprocalSquare_charpoly_eq_of_card_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n ℂ) (h : Fintype.card m ≤ Fintype.card n) :
    (Dᴴ * D).charpoly =
      X ^ (Fintype.card n - Fintype.card m) *
        (D * Dᴴ).charpoly :=
  reciprocalSquare_charpoly_eq_of_card_le D h

/-- Reverse dimension-ordered complex specialization. -/
theorem complex_reciprocalSquare_charpoly_eq_of_card_ge
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n ℂ) (h : Fintype.card n ≤ Fintype.card m) :
    (D * Dᴴ).charpoly =
      X ^ (Fintype.card m - Fintype.card n) *
        (Dᴴ * D).charpoly :=
  reciprocalSquare_charpoly_eq_of_card_ge D h

end GaloisForLFunctions.HTGeometry
