import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# A radical polynomial over a prime is irreducible

The polynomial `X ^ n - q` with `q` prime satisfies the Eisenstein criterion at the ideal generated
by `q`: the leading coefficient is a unit, every lower coefficient is a multiple of `q`, and the
constant one is not a multiple of `q ^ 2`.  So it is irreducible over the domain, and being monic it
stays irreducible over the fraction field.

This covers every exponent, in particular the even ones that the general criterion for radical
polynomials does not yet reach.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

omit [UniqueFactorizationMonoid A] in
theorem isEisensteinAt_X_pow_sub_C {q : A} (hq : Prime q) {n : ℕ} (hn : 0 < n) :
    (Polynomial.X ^ n - Polynomial.C q : Polynomial A).IsEisensteinAt (Ideal.span {q}) where
  leading := by
    rw [(Polynomial.monic_X_pow_sub_C q (by omega)).leadingCoeff]
    intro hcon
    exact hq.not_unit (isUnit_of_dvd_one (Ideal.mem_span_singleton.1 hcon))
  mem := by
    intro k hk
    rw [Polynomial.natDegree_X_pow_sub_C] at hk
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega), Polynomial.coeff_C]
    by_cases hk0 : k = 0
    · rw [if_pos hk0, zero_sub]
      exact Ideal.mem_span_singleton.2 ⟨-1, by ring⟩
    · rw [if_neg hk0, zero_sub, neg_zero]
      exact Ideal.zero_mem _
  notMem := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega), Polynomial.coeff_C,
      if_pos rfl, zero_sub]
    intro hcon
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hcon
    obtain ⟨t, ht⟩ := hcon
    have hdvd : q * q ∣ q := ⟨-t, by rw [pow_two] at ht; linear_combination -ht⟩
    obtain ⟨u, hu⟩ := hdvd
    have hone : q * 1 = q * (q * u) := by linear_combination hu
    have h1 : (1 : A) = q * u := mul_left_cancel₀ hq.ne_zero hone
    exact hq.not_unit (isUnit_of_dvd_one ⟨u, h1⟩)

/-- **A radical polynomial over a prime is irreducible over the fraction field.** -/
theorem irreducible_X_pow_sub_C_of_prime {q : A} (hq : Prime q) {n : ℕ} (hn : 0 < n) :
    Irreducible (Polynomial.X ^ n -
      Polynomial.C (algebraMap A (FractionRing A) q) : Polynomial (FractionRing A)) := by
  have hmonic : (Polynomial.X ^ n - Polynomial.C q : Polynomial A).Monic :=
    Polynomial.monic_X_pow_sub_C q (by omega)
  have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C q : Polynomial A) :=
    (isEisensteinAt_X_pow_sub_C hq hn).irreducible
      (Ideal.span_singleton_prime hq.ne_zero |>.2 hq) hmonic.isPrimitive
      (by rw [Polynomial.natDegree_X_pow_sub_C]; omega)
  have hmap : Polynomial.map (algebraMap A (FractionRing A))
      (Polynomial.X ^ n - Polynomial.C q : Polynomial A) =
      Polynomial.X ^ n - Polynomial.C (algebraMap A (FractionRing A) q) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [← hmap]
  exact (hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map).1 hirr

end GaloisForLFunctions.HTGeometry
