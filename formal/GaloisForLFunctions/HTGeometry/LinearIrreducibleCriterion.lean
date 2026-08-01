import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# A linear polynomial with coprime coefficients is irreducible

A polynomial of degree one is primitive exactly when its two coefficients have no common factor, and
over a unique factorisation domain a primitive polynomial is irreducible exactly when it is
irreducible over the fraction field, where degree one already suffices.

So a determinant expanded as a variable times a cofactor plus a remainder is irreducible as soon as
the cofactor and the remainder are coprime.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
theorem isPrimitive_linear_of_isCoprime {A B : R} (hcop : IsCoprime A B) :
    (Polynomial.C A * Polynomial.X + Polynomial.C B).IsPrimitive := by
  intro r hr
  have hA : r ∣ A := by
    obtain ⟨q, hq⟩ := hr
    refine ⟨q.coeff 1, ?_⟩
    have h := congrArg (fun p : Polynomial R => p.coeff 1) hq
    simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_one,
      Polynomial.coeff_C] using h
  have hB : r ∣ B := by
    obtain ⟨q, hq⟩ := hr
    refine ⟨q.coeff 0, ?_⟩
    have h := congrArg (fun p : Polynomial R => p.coeff 0) hq
    simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_C] using h
  exact hcop.isUnit_of_dvd' hA hB

/-- **A linear polynomial with coprime coefficients is irreducible.** -/
theorem irreducible_linear_of_isCoprime [IsGCDMonoid R] {A B : R} (hA : A ≠ 0)
    (hcop : IsCoprime A B) :
    Irreducible (Polynomial.C A * Polynomial.X + Polynomial.C B) := by
  have hprim := isPrimitive_linear_of_isCoprime hcop
  rw [hprim.irreducible_iff_irreducible_map_fraction_map (K := FractionRing R)]
  refine Polynomial.irreducible_of_degree_eq_one ?_
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_C]
  refine Polynomial.degree_linear ?_
  exact fun h => hA ((IsFractionRing.injective R (FractionRing R)) (by simpa using h))

/-! ## The criterion with the gcd hypothesis

Over a unique factorisation domain the relevant hypothesis is that the two coefficients have no
common factor, which is weaker than the Bezout condition `IsCoprime` and is what the determinant
expansion can supply. -/

omit [IsDomain R] in
theorem isPrimitive_linear_of_isUnit_gcd [GCDMonoid R] {A B : R}
    (h : IsUnit (gcd A B)) :
    (Polynomial.C A * Polynomial.X + Polynomial.C B).IsPrimitive := by
  intro r hr
  have hA : r ∣ A := by
    obtain ⟨q, hq⟩ := hr
    refine ⟨q.coeff 1, ?_⟩
    have hc := congrArg (fun p : Polynomial R => p.coeff 1) hq
    simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_one,
      Polynomial.coeff_C] using hc
  have hB : r ∣ B := by
    obtain ⟨q, hq⟩ := hr
    refine ⟨q.coeff 0, ?_⟩
    have hc := congrArg (fun p : Polynomial R => p.coeff 0) hq
    simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_C] using hc
  exact isUnit_of_dvd_unit (dvd_gcd hA hB) h

/-- **A linear polynomial whose coefficients have no common factor is irreducible.** -/
theorem irreducible_linear_of_isUnit_gcd [GCDMonoid R] {A B : R} (hA : A ≠ 0)
    (h : IsUnit (gcd A B)) :
    Irreducible (Polynomial.C A * Polynomial.X + Polynomial.C B) := by
  have hprim := isPrimitive_linear_of_isUnit_gcd h
  rw [hprim.irreducible_iff_irreducible_map_fraction_map (K := FractionRing R)]
  refine Polynomial.irreducible_of_degree_eq_one ?_
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_C]
  refine Polynomial.degree_linear ?_
  exact fun hc => hA ((IsFractionRing.injective R (FractionRing R)) (by simpa using hc))

omit [IsDomain R] in
/-- **A common factor is excluded by one point.**  If a specialisation kills the cofactor but not the
remainder, the cofactor does not divide the remainder. -/
theorem not_dvd_of_map_eq_zero_of_map_ne_zero {S : Type*} [CommRing S] (f : R →+* S) {A B : R}
    (hA : f A = 0) (hB : f B ≠ 0) : ¬ A ∣ B := by
  rintro ⟨C, rfl⟩
  rw [map_mul, hA, zero_mul] at hB
  exact hB rfl

/-! ## The criterion without a chosen gcd

A polynomial ring in several variables carries no canonical gcd, so the usable form of the hypothesis
is that every common divisor of the two coefficients is a unit. -/

omit [IsDomain R] in
theorem isPrimitive_linear_of_forall_isUnit {A B : R}
    (h : ∀ r : R, r ∣ A → r ∣ B → IsUnit r) :
    (Polynomial.C A * Polynomial.X + Polynomial.C B).IsPrimitive := by
  intro r hr
  have hA : r ∣ A := by
    obtain ⟨q, hq⟩ := hr
    refine ⟨q.coeff 1, ?_⟩
    have hc := congrArg (fun p : Polynomial R => p.coeff 1) hq
    simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_one,
      Polynomial.coeff_C] using hc
  have hB : r ∣ B := by
    obtain ⟨q, hq⟩ := hr
    refine ⟨q.coeff 0, ?_⟩
    have hc := congrArg (fun p : Polynomial R => p.coeff 0) hq
    simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_C] using hc
  exact h r hA hB

/-- **A linear polynomial over a unique factorisation domain is irreducible when its coefficients
have only unit common divisors.** -/
theorem irreducible_linear_of_forall_isUnit [UniqueFactorizationMonoid R] {A B : R} (hA : A ≠ 0)
    (h : ∀ r : R, r ∣ A → r ∣ B → IsUnit r) :
    Irreducible (Polynomial.C A * Polynomial.X + Polynomial.C B) := by
  classical
  letI := UniqueFactorizationMonoid.toGCDMonoid R
  have hprim := isPrimitive_linear_of_forall_isUnit h
  rw [hprim.irreducible_iff_irreducible_map_fraction_map (K := FractionRing R)]
  refine Polynomial.irreducible_of_degree_eq_one ?_
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_C]
  refine Polynomial.degree_linear ?_
  exact fun hc => hA ((IsFractionRing.injective R (FractionRing R)) (by simpa using hc))

end GaloisForLFunctions.HTGeometry
