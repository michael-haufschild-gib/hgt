import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusPolynomialPrimitives
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Rational Frobenius primitives are polynomial

If `f^m-f` is polynomial and `m>1`, the rational function `f` is integral
over the polynomial ring, hence polynomial. This transfers the complete
classification of polynomial Frobenius primitives to rational functions:
the periods divide, and every primitive is the trace polynomial plus a
Frobenius-fixed constant.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K : Type*} [Field K]

/-- A nonconstant monic polynomial over `K[X]` detects polynomial rational functions. -/
theorem ratFunc_monic_aeval_polynomial_iff (F : K[X][X])
    (hF : F.Monic) (hdeg : F.natDegree ≠ 0) (f : RatFunc K) :
    (∃ g : K[X], algebraMap K[X] (RatFunc K) g = aeval f F) ↔
      ∃ P : K[X], algebraMap K[X] (RatFunc K) P = f := by
  constructor
  · intro hg
    apply IsIntegrallyClosed.isIntegral_iff.mp
    exact IsIntegral.of_aeval_monic hF hdeg (IsIntegrallyClosed.isIntegral_iff.mpr hg)
  · rintro ⟨P, rfl⟩
    exact ⟨F.eval P, (eval₂_at_apply (algebraMap K[X] (RatFunc K)) P).symm⟩

/-- A rational function with polynomial power difference has no finite poles. -/
theorem ratFunc_polynomial_of_power_sub (m : ℕ) (hm : 1 < m) (f : RatFunc K) (g : K[X])
    (hf : f ^ m - f = algebraMap K[X] (RatFunc K) g) :
    ∃ P : K[X], algebraMap K[X] (RatFunc K) P = f := by
  apply IsIntegrallyClosed.isIntegral_iff.mp
  refine ⟨X ^ m - (X + C g), monic_X_pow_sub ?_, ?_⟩
  · rw [degree_X_add_C]
    exact_mod_cast hm
  · simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_add, eval₂_C]
    linear_combination hf

/-- Polynomiality of a nontrivial power difference detects polynomiality of the rational function. -/
theorem ratFunc_power_difference_polynomial_iff (n : ℕ) (f : RatFunc K) :
    (∃ g : K[X], f ^ (n + 2) - f = algebraMap K[X] (RatFunc K) g) ↔
      ∃ P : K[X], algebraMap K[X] (RatFunc K) P = f := by
  constructor
  · rintro ⟨g, hg⟩
    exact ratFunc_polynomial_of_power_sub (n + 2) (by omega) f g hg
  · rintro ⟨P, rfl⟩
    exact ⟨P ^ (n + 2) - P, by rw [map_sub, map_pow]⟩

/-- The degree of a nonconstant polynomial power difference is divisible by its exponent. -/
theorem ratFunc_power_sub_degree (m : ℕ) (hm : 1 < m) (f : RatFunc K) (g : K[X])
    (hf : f ^ m - f = algebraMap K[X] (RatFunc K) g) :
    g.natDegree = 0 ∨ m ∣ g.natDegree := by
  obtain ⟨P, hP⟩ := ratFunc_polynomial_of_power_sub m hm f g hf
  have hg : P ^ m - P = g := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    simpa only [map_sub, map_pow, hP] using hf
  by_cases hd : P.natDegree = 0
  · left
    rw [eq_C_of_natDegree_eq_zero hd, ← map_pow, ← map_sub] at hg
    rw [← hg, natDegree_C]
  · right
    have hlt : P.natDegree < (P ^ m).natDegree := by
      rw [natDegree_pow]
      nlinarith only [hm, Nat.pos_of_ne_zero hd]
    refine ⟨P.natDegree, ?_⟩
    rw [← hg, natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_pow]

/-- Monomials of degree one modulo the exponent have no rational power-difference primitive. -/
theorem ratFunc_monomial_power_difference_obstruction (n t : ℕ) :
    ¬ ∃ f : RatFunc K, f ^ (n + 2) - f =
      algebraMap K[X] (RatFunc K) (X ^ ((n + 2) * t + 1)) := by
  rintro ⟨f, hf⟩
  have hd := ratFunc_power_sub_degree (n + 2) (by omega) f _ hf
  rw [natDegree_X_pow] at hd
  rcases hd with hd | hd
  · omega
  · rw [Nat.dvd_iff_mod_eq_zero] at hd
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt (show 1 < n + 2 by omega)] at hd
    omega

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Rational Frobenius primitives have exactly the same trace classification as polynomial ones. -/
theorem ratFunc_frobenius_primitive_iff (r n : ℕ) (f : RatFunc K) :
    f ^ p ^ (r + 1) - f = algebraMap K[X] (RatFunc K) (X ^ p ^ n - X) ↔
      r + 1 ∣ n ∧ ∃ a : K, a ^ p ^ (r + 1) = a ∧
        f = algebraMap K[X] (RatFunc K)
          (frobeniusTraceSum p (r + 1) (n / (r + 1)) X + C a) := by
  constructor
  · intro hf
    obtain ⟨P, hP⟩ := ratFunc_polynomial_of_power_sub (p ^ (r + 1))
      (Nat.one_lt_pow (Nat.succ_ne_zero r) (Fact.out : p.Prime).one_lt) f _ hf
    have hpoly : P ^ p ^ (r + 1) - P = X ^ p ^ n - X := by
      apply IsFractionRing.injective K[X] (RatFunc K)
      simpa only [map_sub, map_pow, hP] using hf
    obtain ⟨hd, a, ha, he⟩ := (polynomial_frobenius_primitive_iff p r n P).mp hpoly
    exact ⟨hd, a, ha, by rw [← hP, he]⟩
  · rintro ⟨hd, a, ha, rfl⟩
    have hp := (polynomial_frobenius_primitive_iff p r n
      (frobeniusTraceSum p (r + 1) (n / (r + 1)) (X : K[X]) + C a)).mpr
      ⟨hd, a, ha, rfl⟩
    simpa only [map_sub, map_pow] using congrArg (algebraMap K[X] (RatFunc K)) hp

/-- Allowing rational functions does not remove the Frobenius period obstruction. -/
theorem exists_ratFunc_frobenius_primitive_iff (r n : ℕ) :
    (∃ f : RatFunc K, f ^ p ^ (r + 1) - f =
      algebraMap K[X] (RatFunc K) (X ^ p ^ n - X)) ↔ r + 1 ∣ n := by
  constructor
  · rintro ⟨f, hf⟩
    exact ((ratFunc_frobenius_primitive_iff p r n f).mp hf).1
  · intro hd
    refine ⟨algebraMap K[X] (RatFunc K)
      (frobeniusTraceSum p (r + 1) (n / (r + 1)) X), ?_⟩
    apply (ratFunc_frobenius_primitive_iff p r n _).mpr
    refine ⟨hd, 0, ?_, ?_⟩
    · exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    · rw [map_zero, add_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ratFunc_polynomial_of_power_sub
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ratFunc_power_difference_polynomial_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ratFunc_frobenius_primitive_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_ratFunc_frobenius_primitive_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ratFunc_monic_aeval_polynomial_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ratFunc_power_sub_degree
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ratFunc_monomial_power_difference_obstruction
