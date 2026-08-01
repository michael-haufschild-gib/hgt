import GaloisForLFunctions.HTGeometry.PolynomialNonSquare
import Mathlib.RingTheory.Localization.NumDen

/-!
# A prime is not a proper power in the fraction field

Writing a candidate root as a reduced fraction, a `p`-th power equal to a prime forces the prime to
divide both numerator and denominator, which a reduced fraction forbids.

Applied to a variable of a polynomial ring this says a variable is not a proper power in the
rational function field, which is the input of the irreducibility criterion for radical
polynomials.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A prime of a unique factorisation domain is not a proper power in the fraction field.** -/
theorem not_pow_eq_of_prime {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    {q : A} (hq : Prime q) {p : ℕ} (hp : 2 ≤ p) (b : FractionRing A) :
    b ^ p ≠ algebraMap A (FractionRing A) q := by
  intro hb
  obtain ⟨a, d, hrel, hab⟩ :=
    IsFractionRing.exists_reduced_fraction (K := FractionRing A) A b
  have hdne : (d : A) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hdF : algebraMap A (FractionRing A) (d : A) ≠ 0 := fun hcon =>
    hdne (IsFractionRing.injective _ _ (by rw [hcon, map_zero]))
  have hspec : b * algebraMap A (FractionRing A) (d : A) = algebraMap A (FractionRing A) a := by
    rw [← hab]
    exact IsLocalization.mk'_spec _ _ _
  have hfrac : algebraMap A (FractionRing A) (a ^ p) =
      algebraMap A (FractionRing A) (q * (d : A) ^ p) := by
    rw [map_mul, map_pow, map_pow, ← hb, ← hspec, mul_pow]
  have hring : a ^ p = q * (d : A) ^ p := IsFractionRing.injective A (FractionRing A) hfrac
  have hqa : q ∣ a := hq.dvd_of_dvd_pow ⟨(d : A) ^ p, hring⟩
  obtain ⟨a', ha'⟩ := hqa
  have hcancel : q ^ (p - 1) * a' ^ p = (d : A) ^ p := by
    have hpow : q ^ p = q * q ^ (p - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h : q * (q ^ (p - 1) * a' ^ p) = q * (d : A) ^ p := by
      rw [← mul_assoc, ← hpow, ← mul_pow, ← ha', hring]
    exact mul_left_cancel₀ hq.ne_zero h
  have hqd : q ∣ (d : A) := by
    refine hq.dvd_of_dvd_pow (n := p) ?_
    refine ⟨q ^ (p - 1 - 1) * a' ^ p, ?_⟩
    rw [← hcancel, ← mul_assoc, ← pow_succ']
    congr 2
    omega
  exact hq.not_unit (hrel ⟨a', ha'⟩ hqd)

/-- **A variable is not a proper power in the rational function field.** -/
theorem not_pow_eq_X {σ K : Type*} [Field K] {p : ℕ} (hp : 2 ≤ p) (i : σ)
    (b : FractionRing (MvPolynomial σ K)) :
    b ^ p ≠ algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      (MvPolynomial.X i) :=
  not_pow_eq_of_prime MvPolynomial.X_prime hp b

end GaloisForLFunctions.HTGeometry
