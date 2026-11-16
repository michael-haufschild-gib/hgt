import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Polynomial.Derivative


/-!
# Degree and differential of Frobenius trace polynomials

A nonempty Frobenius trace polynomial is monic, with degree given by its
last Frobenius power. In characteristic `p` its derivative is one. Thus
trace substitution preserves transcendence and is separable.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial
open scoped nonZeroDivisors
variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K]

private theorem trace_polynomial_leading (d m : ℕ) :
    (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])).Monic ∧
    (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])).natDegree = p ^ ((d + 1) * m) := by
  induction m with
  | zero =>
    simp only [frobeniusTraceSum, zero_add, Finset.sum_range_one,
      Nat.mul_zero, pow_zero, pow_one]
    exact ⟨monic_X, natDegree_X⟩
  | succ m ih =>
    have hs : frobeniusTraceSum p (d + 1) (m + 1 + 1) (X : K[X]) =
        frobeniusTraceSum p (d + 1) (m + 1) X + X ^ p ^ ((d + 1) * (m + 1)) :=
      Finset.sum_range_succ _ _
    have hlt : (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])).natDegree <
        (X ^ p ^ ((d + 1) * (m + 1)) : K[X]).natDegree := by
      rw [ih.2, natDegree_X_pow]
      exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
        (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self m) (Nat.succ_pos d))
    rw [hs]
    have hdegree := natDegree_add_eq_right_of_natDegree_lt hlt
    constructor
    · change (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X]) +
        X ^ p ^ ((d + 1) * (m + 1))).leadingCoeff = 1
      rw [leadingCoeff, hdegree, coeff_add_eq_right_of_lt hlt, natDegree_X_pow, coeff_X_pow_self]
    · simpa only [natDegree_X_pow] using hdegree

/-- The trace polynomial is monic, so its leading coefficient never disappears. -/
theorem frobeniusTraceSum_polynomial_monic (d m : ℕ) :
    (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])).Monic :=
  (trace_polynomial_leading p d m).1

/-- The trace polynomial's exact degree is its last Frobenius exponent. -/
theorem frobeniusTraceSum_polynomial_natDegree (d m : ℕ) :
    (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])).natDegree = p ^ ((d + 1) * m) :=
  (trace_polynomial_leading p d m).2

/-- Trace substitution of a transcendental element remains transcendental. -/
theorem frobeniusTraceSum_transcendental {L : Type*} [Field L] [Algebra K L]
    (d m : ℕ) {x : L} (hx : Transcendental K x) :
    Transcendental K (frobeniusTraceSum p (d + 1) (m + 1) x) := by
  have h := hx.aeval (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X]))
    (by rw [frobeniusTraceSum_polynomial_natDegree]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    (by rw [(frobeniusTraceSum_polynomial_monic (K := K) p d m).leadingCoeff]; exact one_mem _)
  simpa only [frobeniusTraceSum, map_sum, map_pow, aeval_X] using h

/-- In characteristic `p`, every higher Frobenius term has zero derivative and the linear term survives. -/
theorem frobeniusTraceSum_polynomial_derivative [CharP K p] (d m : ℕ) :
    derivative (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])) = 1 := by
  induction m with
  | zero => simp only [frobeniusTraceSum, zero_add, Finset.sum_range_one,
      Nat.mul_zero, pow_zero, pow_one, derivative_X]
  | succ m ih =>
    have hs : frobeniusTraceSum p (d + 1) (m + 1 + 1) (X : K[X]) =
        frobeniusTraceSum p (d + 1) (m + 1) X + X ^ p ^ ((d + 1) * (m + 1)) :=
      Finset.sum_range_succ _ _
    rw [hs, derivative_add, ih, derivative_X_pow]
    have hcast : ((p ^ ((d + 1) * (m + 1)) : ℕ) : K) = 0 := by
      rw [Nat.cast_pow, CharP.cast_eq_zero K p,
        zero_pow (Nat.mul_ne_zero (Nat.succ_ne_zero d) (Nat.succ_ne_zero m))]
    simp only [hcast, map_zero, zero_mul, add_zero]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
