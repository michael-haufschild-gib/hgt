import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Squares descend along a specialisation whose kernel is a prime

Writing an element of a fraction field as a reduced fraction, a square in the fraction field of a
unique factorisation domain gives a square relation in the domain itself.  Applying a ring
homomorphism whose kernel consists of multiples of a prime cannot kill the denominator: that would
force the prime to divide both numerator and denominator, which a reduced fraction forbids.

So the image of the element is again a square, and contrapositively a nonsquare image certifies a
nonsquare.  This transports square classes along a specialisation that sets one variable to zero.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Squares descend along a prime specialisation.**  If the image of `u` is not a square in the
fraction field of the target, then `u` is not a square in the fraction field of the source. -/
theorem not_isSquare_of_specialisation
    {A B : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing B] [IsDomain B]
    (φ : A →+* B) {p : A} (hp : Prime p)
    (hker : ∀ a : A, φ a = 0 → p ∣ a)
    {u : A}
    (hu : ¬ IsSquare (algebraMap B (FractionRing B) (φ u))) :
    ¬ IsSquare (algebraMap A (FractionRing A) u) := by
  rintro ⟨t, ht⟩
  obtain ⟨a, b, hrel, hab⟩ :=
    IsFractionRing.exists_reduced_fraction (K := FractionRing A) A t
  have hspec : t * algebraMap A (FractionRing A) (b : A) =
      algebraMap A (FractionRing A) a := by
    rw [← hab]
    exact IsLocalization.mk'_spec _ _ _
  have hfrac : algebraMap A (FractionRing A) (u * (b : A) * (b : A)) =
      algebraMap A (FractionRing A) (a * a) := by
    rw [map_mul, map_mul, map_mul, ht]
    calc t * t * algebraMap A (FractionRing A) (b : A) *
          algebraMap A (FractionRing A) (b : A)
        = (t * algebraMap A (FractionRing A) (b : A)) *
          (t * algebraMap A (FractionRing A) (b : A)) := by ring
      _ = algebraMap A (FractionRing A) a * algebraMap A (FractionRing A) a := by rw [hspec]
  have hA : u * (b : A) * (b : A) = a * a :=
    IsFractionRing.injective A (FractionRing A) hfrac
  have hbne : φ (b : A) ≠ 0 := by
    intro hb0
    have hpb : p ∣ (b : A) := hker _ hb0
    have hpa : p ∣ a := by
      refine hp.dvd_of_dvd_pow (n := 2) ?_
      rw [pow_two, ← hA]
      exact hpb.mul_left (u * (b : A))
    exact hp.not_unit (hrel hpa hpb)
  have hB : φ u * φ (b : A) * φ (b : A) = φ a * φ a := by
    rw [← map_mul, ← map_mul, ← map_mul, hA]
  refine hu ⟨algebraMap B (FractionRing B) (φ a) / algebraMap B (FractionRing B) (φ (b : A)), ?_⟩
  have hbF : algebraMap B (FractionRing B) (φ (b : A)) ≠ 0 := by
    intro hcon
    exact hbne (IsFractionRing.injective B (FractionRing B) (by rw [hcon, map_zero]))
  field_simp
  have := congrArg (algebraMap B (FractionRing B)) hB
  rw [map_mul, map_mul, map_mul] at this
  linear_combination this

end GaloisForLFunctions.HTGeometry
