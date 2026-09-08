import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy
import GaloisForLFunctions.HTGeometry.SquareIndexSymmetricSquare
import GaloisForLFunctions.HTGeometry.QNMHyperboloidalPolynomial
/-!
# Symmetric-power and hyperboloidal-wave applications of the cavity hierarchy

The recurrence from arXiv:2608.14343 agrees with the existing two-variable
complete homogeneous character. This transfers symmetric-square index selection
and gives a finite local-factor remainder. Its second-kind Chebyshev polynomials
also supply a new exact basis identity for the corpus hyperboloidal wave operator.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
/-- The cavity recurrence is the complete homogeneous character of its two roots. -/
theorem quadraticResponseCoeff_eq_hSym {R : Type*} [CommRing R] (a b : R) (n : ℕ) :
    quadraticResponseCoeff (-(a + b)) (a * b) n = _root_.HTGeometry.hSym a b n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [_root_.HTGeometry.hSym_succ]
  | more n h0 h1 =>
      rw [quadraticResponseCoeff_add_two, h0, h1]
      have hs0 := _root_.HTGeometry.hSym_succ a b n
      have hs1 := _root_.HTGeometry.hSym_succ a b (n + 1)
      change _ = _root_.HTGeometry.hSym a b ((n + 1) + 1)
      rw [hs1, pow_succ a (n + 1)]
      linear_combination a * hs0
/-- The symmetric-square even-index law transfers to the cavity response at all orders. -/
theorem quadraticResponseCoeff_even_selection {R : Type*} [CommRing R] (a b : R) (n : ℕ) :
    quadraticResponseCoeff (-(a + b)) (a * b) (2 * n + 2) =
      quadraticResponseCoeff (-(a ^ 2 + b ^ 2)) (a ^ 2 * b ^ 2) (n + 1) +
        a * b * quadraticResponseCoeff (-(a ^ 2 + b ^ 2)) (a ^ 2 * b ^ 2) n := by
  simp only [quadraticResponseCoeff_eq_hSym]
  exact _root_.HTGeometry.hSym_two_mul a b n
/-- An exact finite local-factor expansion for arbitrary roots, including repeated and zero roots. -/
theorem hSym_cavity_finite_remainder {R : Type*} [CommRing R] (a b z : R) (n : ℕ) :
    ((1 - a * z) * (1 - b * z)) *
        (∑ k ∈ Finset.range (n + 1), _root_.HTGeometry.hSym a b k * z ^ k) =
      1 - _root_.HTGeometry.hSym a b (n + 1) * z ^ (n + 1) +
        a * b * _root_.HTGeometry.hSym a b n * z ^ (n + 2) := by
  have h := quadraticResponseCoeff_finite_remainder (-(a + b)) (a * b) z n
  simp only [quadraticResponseCoeff_eq_hSym] at h
  convert h using 1; ring
/-- The second-kind cavity polynomial has a closed hyperboloidal squared-derivative law. -/
theorem qnmHyperboloidalDx_squared_cavityChebyshev
    {R : Type*} [CommRing R] (z : R) (n : ℤ) :
    qnmHyperboloidalDx z (qnmHyperboloidalDx z (Polynomial.Chebyshev.U R n)) =
      (1 - 2 * Polynomial.C z) * Polynomial.X * (1 - Polynomial.X ^ 2) *
        (Polynomial.Chebyshev.U R n).derivative +
      (Polynomial.C z ^ 2 * Polynomial.X ^ 2 -
        ((n : Polynomial R) * ((n : Polynomial R) + 2) + Polynomial.C z) * (1 - Polynomial.X ^ 2)) *
          Polynomial.Chebyshev.U R n := by
  rw [qnmHyperboloidalDx_squared]
  have h := Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R := R) n
  change (1 - Polynomial.X ^ 2) * (Polynomial.Chebyshev.U R n).derivative.derivative =
    3 * Polynomial.X * (Polynomial.Chebyshev.U R n).derivative -
      (((n : Polynomial R) + 2) * (n : Polynomial R)) * Polynomial.Chebyshev.U R n at h
  linear_combination (1 - Polynomial.X ^ 2) * h
end
end GaloisForLFunctions.HTGeometry
