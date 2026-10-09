import GaloisForLFunctions.HTGeometry.PaperNativeReesSpecialization

/-!
# Every associated-graded class has a native Rees representative

Invert the Laurent variable and truncate to nonnegative powers. This retains
precisely the original nonpositive degrees; all discarded positive degrees
are divisible by the Rees parameter. The resulting representative proves
surjectivity and an actual quotient-algebra equivalence, with an exact
coefficient criterion for both equality and vanishing.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Laurent truncation preserves each nonnegative coefficient definitionally. -/
theorem paperLaurentTrunc_coeff (p : LaurentPolynomial R) (n : ℕ) :
    (LaurentPolynomial.trunc p).coeff n = p.coeff (n : ℤ) := rfl

/-- An explicit native Rees representative for every extended Rees polynomial. -/
def paperNativeReesRepresentative (p : PaperIdealExtendedRees I) : reesAlgebra I :=
  ⟨LaurentPolynomial.trunc (LaurentPolynomial.invert (p : LaurentPolynomial R)), by
    intro n
    rw [paperLaurentTrunc_coeff, LaurentPolynomial.invert_apply]
    have hn := p.property (-(n : ℤ))
    rwa [paperIdealPowerFiltration_neg_nat] at hn⟩

/-- The representative retains exactly the negative Laurent coefficients. -/
theorem paperNativeReesRepresentative_coeff (p : PaperIdealExtendedRees I) (n : ℕ) :
    (paperNativeReesRepresentative I p : Polynomial R).coeff n =
      (p : LaurentPolynomial R).coeff (-(n : ℤ)) := by
  change (LaurentPolynomial.trunc (LaurentPolynomial.invert (p : LaurentPolynomial R))).coeff n = _
  rw [paperLaurentTrunc_coeff, LaurentPolynomial.invert_apply]

/-- Discarding the positive Laurent terms does not change the associated-graded class. -/
theorem paperNativeReesRepresentative_specialization (p : PaperIdealExtendedRees I) :
    paperNativeReesSpecialization I (paperNativeReesRepresentative I p) =
      Ideal.Quotient.mk
        (FilteredRees.parameterIdeal (paperIdealPowerFiltration I) (paperIdealPowerFiltration_mono I)) p := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk _ (paperNativeReesEmbedding I (paperNativeReesRepresentative I p)) -
    Ideal.Quotient.mk _ p = 0
  have hm := map_sub (Ideal.Quotient.mk
    (FilteredRees.parameterIdeal (paperIdealPowerFiltration I) (paperIdealPowerFiltration_mono I)))
    (paperNativeReesEmbedding I (paperNativeReesRepresentative I p)) p
  rw [← hm, paperIdealExtendedRees_specialization_eq_zero_iff]
  intro d
  change (paperInverseLaurentPolynomial (paperNativeReesRepresentative I p : Polynomial R)).coeff d -
    (p : LaurentPolynomial R).coeff d ∈ I ^ (1 - d).toNat
  by_cases hd : d ≤ 0
  · have he : d = -(((-d).toNat : ℕ) : ℤ) := by omega
    rw [he, paperInverseLaurentPolynomial_coeff_neg_nat, paperNativeReesRepresentative_coeff, sub_self]
    exact (I ^ _).zero_mem
  · have he : (1 - d).toNat = 0 := by omega
    rw [he, pow_zero]
    simp

/-- The native Rees specialization covers the entire associated graded algebra. -/
theorem paperNativeReesSpecialization_surjective : Function.Surjective (paperNativeReesSpecialization I) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective R
    (FilteredRees.parameterIdeal (paperIdealPowerFiltration I) (paperIdealPowerFiltration_mono I)) z
  exact ⟨paperNativeReesRepresentative I p, paperNativeReesRepresentative_specialization I p⟩

/-- The actual ideal of native Rees polynomials whose coefficients gain one ideal order. -/
def paperNativeReesCoefficientIdeal : Ideal (reesAlgebra I) :=
  RingHom.ker (paperNativeReesSpecialization I).toRingHom

/-- Ideal membership is detected at every coefficient, with the exact successor power. -/
theorem paperNativeReesCoefficientIdeal_mem_iff (p : reesAlgebra I) :
    p ∈ paperNativeReesCoefficientIdeal I ↔
      ∀ n : ℕ, (p : Polynomial R).coeff n ∈ I ^ (n + 1) :=
  paperNativeReesSpecialization_eq_zero_iff_coeff I p

/-- The full associated graded algebra is the quotient of the existing native Rees algebra. -/
def paperNativeReesQuotientEquiv :
    (reesAlgebra I ⧸ paperNativeReesCoefficientIdeal I) ≃ₐ[R] PaperIdealAssociatedGraded I :=
  Ideal.quotientKerAlgEquivOfSurjective (paperNativeReesSpecialization_surjective I)

/-- Equality of specialized native Rees elements is exactly coefficientwise congruence. -/
theorem paperNativeReesSpecialization_eq_iff_coeff (p q : reesAlgebra I) :
    paperNativeReesSpecialization I p = paperNativeReesSpecialization I q ↔
      ∀ n : ℕ, (p : Polynomial R).coeff n - (q : Polynomial R).coeff n ∈ I ^ (n + 1) := by
  rw [← sub_eq_zero, ← map_sub, paperNativeReesSpecialization_eq_zero_iff_coeff]
  apply forall_congr'
  intro n
  change ((p : Polynomial R) - (q : Polynomial R)).coeff n ∈ _ ↔ _
  rw [Polynomial.coeff_sub]

/-- The native homogeneous class has exactly the expected `I^n/I^(n+1)` vanishing criterion. -/
theorem paperNativeReesSpecialization_mono_eq_zero_iff (n : ℕ) (a : (I ^ n : Ideal R)) :
    paperNativeReesSpecialization I (ReesGrading.mono I n a a.property) = 0 ↔
      (a : R) ∈ I ^ (n + 1) := by
  rw [paperNativeReesSpecialization_eq_zero_iff_coeff]
  change (∀ m : ℕ, (Polynomial.monomial n (a : R)).coeff m ∈ I ^ (m + 1)) ↔ _
  constructor
  · intro h
    simpa only [Polynomial.coeff_monomial, ↓reduceIte] using h n
  · intro h m
    rw [Polynomial.coeff_monomial]
    split_ifs with hm
    · subst m
      exact h
    · exact (I ^ (m + 1)).zero_mem

end

end GaloisForLFunctions.HTGeometry
