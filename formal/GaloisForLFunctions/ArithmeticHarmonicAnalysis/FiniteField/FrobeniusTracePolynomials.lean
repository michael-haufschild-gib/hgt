import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Trace polynomials and Kummer substitution

The additive polynomial `Σ j < m, X^(p^(d*j))` telescopes under the
`p^d`-power Frobenius. Geometric exponents convert its Artin–Schreier
difference into the right-hand side of a Kummer equation.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset

/-- The relative trace polynomial evaluated at `x`. -/
def frobeniusTraceSum {A : Type*} [CommSemiring A] (p d m : ℕ) (x : A) : A :=
  ∑ j ∈ range m, x ^ p ^ (d * j)

section Trace
variable {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p]

/-- Frobenius telescoping holds before imposing any finite-field equation. -/
theorem frobeniusTraceSum_sub_pow (d m : ℕ) (x : A) :
    frobeniusTraceSum p d m x - (frobeniusTraceSum p d m x) ^ p ^ d =
      x - x ^ p ^ (d * m) := by
  induction m with
  | zero => simp [frobeniusTraceSum]
  | succ m ih =>
    simp only [frobeniusTraceSum, sum_range_succ] at ih ⊢
    rw [add_pow_char_pow]
    have hpow : (x ^ p ^ (d * m)) ^ p ^ d = x ^ p ^ (d * (m + 1)) := by
      rw [← pow_mul, ← pow_add, Nat.mul_add, Nat.mul_one]
    rw [hpow]
    linear_combination ih

/-- Trace is additive over every ring of the given exponential characteristic. -/
theorem frobeniusTraceSum_add (d m : ℕ) (x y : A) :
    frobeniusTraceSum p d m (x + y) =
      frobeniusTraceSum p d m x + frobeniusTraceSum p d m y := by
  simp only [frobeniusTraceSum, add_pow_char_pow, sum_add_distrib]

/-- The trace of an Artin–Schreier difference is its long Frobenius difference. -/
theorem frobeniusTraceSum_sub (d m : ℕ) (x : A) :
    frobeniusTraceSum p d m (x - x ^ p ^ d) = x - x ^ p ^ (d * m) := by
  rw [← frobeniusTraceSum_sub_pow p d m x]
  simp only [frobeniusTraceSum, sub_pow_char_pow, sum_sub_distrib,
    sum_pow_char_pow, ← pow_mul, Nat.mul_comm (p ^ d)]

end Trace

/-- The geometric exponent appearing in a Kummer equation. -/
def kummerExponent (q r : ℕ) : ℕ := ∑ j ∈ range r, q ^ j

/-- A division-free form of `(q-1)R=q^r-1`. -/
theorem kummerExponent_mul_add (b r : ℕ) :
    kummerExponent (b + 1) r * b + 1 = (b + 1) ^ r := by
  exact geom_sum_mul_add b r

/-- The substitution `y=u^R` converts the Kummer branch polynomial into
an `R`-th power of an Artin–Schreier difference. -/
theorem kummer_substitution {A : Type*} [CommRing A] (b r : ℕ) (u : A) :
    (u - u ^ (b + 1) ^ r) ^ kummerExponent (b + 1) r =
      u ^ kummerExponent (b + 1) r *
        (1 - (u ^ kummerExponent (b + 1) r) ^ b) ^ kummerExponent (b + 1) r := by
  have h : u - u ^ (b + 1) ^ r = u * (1 - (u ^ kummerExponent (b + 1) r) ^ b) := by
    rw [← kummerExponent_mul_add b r, pow_succ, pow_mul]
    ring
  rw [h, mul_pow]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
