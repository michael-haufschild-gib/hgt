import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTwoTermObstruction
import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Classification of polynomial Frobenius primitives

A polynomial fixed by a positive Frobenius power is constant: otherwise
its degree would increase. Consequently two Frobenius primitives differ
by a fixed constant. Combined with period divisibility, this classifies
all primitives of a pure two-term Frobenius difference over any integral
domain of the prescribed characteristic.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial
variable (p : ℕ) [Fact p.Prime] {K : Type*} [CommRing K] [IsDomain K]

/-- Polynomials fixed by a nontrivial prime-power exponent are exactly its fixed constants. -/
theorem polynomial_primePower_fixed_iff (r : ℕ) (P : K[X]) :
    P ^ p ^ (r + 1) = P ↔ ∃ a : K, a ^ p ^ (r + 1) = a ∧ P = C a := by
  constructor
  · intro hP
    have hq : 1 < p ^ (r + 1) := Nat.one_lt_pow (Nat.succ_ne_zero r)
      (Fact.out : p.Prime).one_lt
    have hdeg := congrArg Polynomial.natDegree hP
    rw [natDegree_pow] at hdeg
    have hd : P.natDegree = 0 := by
      by_contra hn
      have hlt := Nat.mul_lt_mul_of_pos_right hq (Nat.pos_of_ne_zero hn)
      rw [one_mul, hdeg] at hlt
      exact (Nat.lt_irrefl _) hlt
    refine ⟨P.coeff 0, ?_, eq_C_of_natDegree_eq_zero hd⟩
    have hc := congrArg (fun F : K[X] => F.eval 0) hP
    simpa only [eval_pow, ← coeff_zero_eq_eval_zero] using hc
  · rintro ⟨a, ha, rfl⟩
    rw [← map_pow, ha]

variable [CharP K p]

/-- Two polynomial Frobenius primitives differ exactly by a Frobenius-fixed constant. -/
theorem polynomial_frobenius_difference_eq_iff (r : ℕ) (P Q : K[X]) :
    P ^ p ^ (r + 1) - P = Q ^ p ^ (r + 1) - Q ↔
      ∃ a : K, a ^ p ^ (r + 1) = a ∧ P = Q + C a := by
  constructor
  · intro h
    have hD : (P - Q) ^ p ^ (r + 1) = P - Q := by
      rw [sub_pow_char_pow]
      linear_combination h
    obtain ⟨a, ha, he⟩ := (polynomial_primePower_fixed_iff p r (P - Q)).mp hD
    refine ⟨a, ha, ?_⟩
    linear_combination he
  · rintro ⟨a, ha, rfl⟩
    rw [add_pow_char_pow, ← map_pow, ha]
    ring

/-- At a divisible period, every polynomial primitive is a trace polynomial plus a fixed constant. -/
theorem polynomial_frobenius_primitive_trace_iff (r m : ℕ) (P : K[X]) :
    P ^ p ^ (r + 1) - P = X ^ p ^ ((r + 1) * m) - X ↔
      ∃ a : K, a ^ p ^ (r + 1) = a ∧
        P = frobeniusTraceSum p (r + 1) m X + C a := by
  have ht := frobeniusTraceSum_sub_pow p (r + 1) m (X : K[X])
  have he : (frobeniusTraceSum p (r + 1) m (X : K[X])) ^ p ^ (r + 1) -
      frobeniusTraceSum p (r + 1) m X = X ^ p ^ ((r + 1) * m) - X := by
    linear_combination -ht
  rw [← he]
  exact polynomial_frobenius_difference_eq_iff p r P _

/-- The complete classification: the periods divide, and the primitive is the corresponding trace plus a fixed constant. -/
theorem polynomial_frobenius_primitive_iff (r n : ℕ) (P : K[X]) :
    P ^ p ^ (r + 1) - P = X ^ p ^ n - X ↔
      r + 1 ∣ n ∧ ∃ a : K, a ^ p ^ (r + 1) = a ∧
        P = frobeniusTraceSum p (r + 1) (n / (r + 1)) X + C a := by
  constructor
  · intro hP
    have hd := (exists_polynomial_frobenius_difference_iff p r n).mp ⟨P, hP⟩
    refine ⟨hd, ?_⟩
    apply (polynomial_frobenius_primitive_trace_iff p r (n / (r + 1)) P).mp
    simpa only [Nat.mul_div_cancel' hd] using hP
  · rintro ⟨hd, hP⟩
    have h := (polynomial_frobenius_primitive_trace_iff p r (n / (r + 1)) P).mpr hP
    simpa only [Nat.mul_div_cancel' hd] using h

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
