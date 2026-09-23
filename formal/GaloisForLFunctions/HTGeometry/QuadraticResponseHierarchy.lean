import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic
/-!
# Exact quadratic-response coefficient hierarchy

The Chebyshev generating function in Ainsworth et al., arXiv:2608.14343, Eq. (S14),
identifies the nonlinear cavity hierarchy with a second-order recurrence. These
identities hold over every commutative ring, including degenerate parameters.
The finite remainder is exact and requires no convergence assumption.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {R : Type*}
section Ring
variable [Ring R]
/-- Coefficients of the reciprocal quadratic `1 / (1 + a t + b t²)`. -/
def quadraticResponseCoeff (a b : R) : ℕ → R
  | 0 => 1
  | 1 => -a
  | n + 2 => -a * quadraticResponseCoeff a b (n + 1) - b * quadraticResponseCoeff a b n
@[simp] theorem quadraticResponseCoeff_zero (a b : R) : quadraticResponseCoeff a b 0 = 1 := rfl
@[simp] theorem quadraticResponseCoeff_one (a b : R) : quadraticResponseCoeff a b 1 = -a := rfl
theorem quadraticResponseCoeff_add_two (a b : R) (n : ℕ) :
    quadraticResponseCoeff a b (n + 2) =
      -a * quadraticResponseCoeff a b (n + 1) - b * quadraticResponseCoeff a b n := rfl
end Ring

variable [CommRing R]

/-- Exact finite generating-function identity, valid even at poles and outside the convergence disk. -/
theorem quadraticResponseCoeff_finite_remainder (a b t : R) (n : ℕ) :
    (1 + a * t + b * t ^ (2 : ℕ)) *
        (∑ k ∈ Finset.range (n + 1), quadraticResponseCoeff a b k * t ^ k) =
      1 - quadraticResponseCoeff a b (n + 1) * t ^ (n + 1) +
        b * quadraticResponseCoeff a b n * t ^ (n + 2) := by
  induction n with
  | zero => simp [quadraticResponseCoeff]
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      rw [show n + 1 + 1 = n + 2 by omega, quadraticResponseCoeff_add_two]
      simp only [pow_succ]
      ring
/-- The determinant of adjacent coefficient windows is fixed by the quadratic term. -/
theorem quadraticResponseCoeff_cassini (a b : R) (n : ℕ) :
    quadraticResponseCoeff a b (n + 1) ^ (2 : ℕ) -
      quadraticResponseCoeff a b n * quadraticResponseCoeff a b (n + 2) = b ^ (n + 1) := by
  induction n with
  | zero => simp [quadraticResponseCoeff]; ring
  | succ n ih =>
      have h0 := quadraticResponseCoeff_add_two a b n
      have h1 := quadraticResponseCoeff_add_two a b (n + 1)
      rw [show n + 1 + 1 = n + 2 by omega, pow_succ b (n + 1)]
      rw [h1, h0]
      rw [h0] at ih
      linear_combination b * ih
/-- The coefficient hierarchy scales homogeneously at every order. -/
theorem quadraticResponseCoeff_scale (a b r : R) (n : ℕ) :
    quadraticResponseCoeff (r * a) (r ^ (2 : ℕ) * b) n = r ^ n * quadraticResponseCoeff a b n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
      rw [quadraticResponseCoeff_add_two, quadraticResponseCoeff_add_two, h0, h1]
      simp only [pow_succ]
      ring
/-- The Chebyshev hierarchy of arXiv:2608.14343, Eq. (S14), without analytic assumptions. -/
theorem quadraticResponseCoeff_eq_chebyshev (x : R) (n : ℕ) :
    quadraticResponseCoeff (-(2 * x)) 1 n = (Polynomial.Chebyshev.U R n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
      rw [quadraticResponseCoeff_add_two, h0, h1]
      have h := congrArg (Polynomial.eval x) (Polynomial.Chebyshev.U_add_two R (n : ℤ))
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X] at h
      convert h.symm using 1 <;> simp [Nat.cast_add]
/-- Damped Chebyshev coefficients are precisely the general quadratic-response hierarchy. -/
theorem quadraticResponseCoeff_eq_scaled_chebyshev (x r : R) (n : ℕ) :
    quadraticResponseCoeff (-(2 * x * r)) (r ^ (2 : ℕ)) n =
      r ^ n * (Polynomial.Chebyshev.U R n).eval x := by
  rw [show -(2 * x * r) = r * -(2 * x) by ring,
    show r ^ (2 : ℕ) = r ^ (2 : ℕ) * (1 : R) by ring,
    quadraticResponseCoeff_scale, quadraticResponseCoeff_eq_chebyshev]
end
end GaloisForLFunctions.HTGeometry
