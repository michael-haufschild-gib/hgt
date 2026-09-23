import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# An element divisible by a prime exactly once is not a square

In an integrally closed domain a square root in the fraction field of an element of the ring
already lies in the ring.  If a prime divides that element exactly once, the
square root would have to be divisible by the prime, forcing the prime to divide the element twice.

So exact divisibility by one prime certifies a nonsquare, which is how a discriminant is shown not
to become a square after a base change.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A square root in the fraction field of an element of the ring lies in the ring. -/
theorem exists_algebraMap_of_sq_eq {x : R} {z : K} (hz : z * z = algebraMap R K x) :
    ∃ w : R, algebraMap R K w = z := by
  have hint : IsIntegral R z := by
    refine ⟨Polynomial.X ^ (2 : ℕ) - Polynomial.C x, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow 2).sub_of_left (by
        refine lt_of_le_of_lt (Polynomial.degree_C_le) ?_
        rw [Polynomial.degree_X_pow]
        exact WithBot.coe_lt_coe.2 (by norm_num))
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        pow_two, hz, sub_self]
  exact IsIntegrallyClosed.isIntegral_iff.1 hint

/-- **Exact divisibility by a prime certifies a nonsquare.** -/
theorem not_isSquare_of_prime_dvd_once {p x y : R} (hp : Prime p) (hxy : x = p * y)
    (hpy : ¬ p ∣ y) : ¬ IsSquare (algebraMap R K x) := by
  rintro ⟨z, hz⟩
  obtain ⟨w, hw⟩ := exists_algebraMap_of_sq_eq (x := x) (z := z) hz.symm
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hw2 : w * w = x := by
    refine hinj ?_
    rw [map_mul, hw, ← hz]
  have hpw : p ∣ w := by
    refine (hp.dvd_mul.1 ?_).elim id id
    rw [hw2, hxy]
    exact Dvd.intro y rfl
  obtain ⟨u, hu⟩ := hpw
  refine hpy ?_
  have hcancel : p * y = p * (p * (u * u)) := by
    rw [← hxy, ← hw2, hu]
    ring
  have hp0 : p ≠ 0 := hp.ne_zero
  have hy : y = p * (u * u) := mul_left_cancel₀ hp0 hcancel
  exact ⟨u * u, hy⟩

end GaloisForLFunctions.HTGeometry
