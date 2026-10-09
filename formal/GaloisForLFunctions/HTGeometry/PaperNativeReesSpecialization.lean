import GaloisForLFunctions.HTGeometry.PaperIdealPowerReesFiltration

/-!
# Exact associated-graded specialization of the native Rees algebra

Send the native polynomial Rees variable to the inverse Laurent parameter.
The paper's coefficient-kernel theorem then says precisely that a native Rees
element vanishes on the special fibre when its degree-`n` coefficient belongs
to `I^(n+1)`. No domain, finite-generation or Noetherian premise is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable {R : Type*} [CommRing R]

/-- Substitute the inverse Laurent parameter into an ordinary polynomial. -/
def paperInverseLaurentPolynomial : Polynomial R →ₐ[R] LaurentPolynomial R :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

/-- Natural polynomial coefficients become negative Laurent coefficients exactly. -/
theorem paperInverseLaurentPolynomial_coeff_neg_nat (p : Polynomial R) (n : ℕ) :
    (paperInverseLaurentPolynomial p).coeff (-(n : ℤ)) = p.coeff n := by
  change (LaurentPolynomial.invert (Polynomial.toLaurent p)).coeff (-(n : ℤ)) = _
  rw [LaurentPolynomial.invert_apply, neg_neg, LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ n

/-- The inverted polynomial has no positive Laurent coefficients. -/
theorem paperInverseLaurentPolynomial_coeff_pos (p : Polynomial R) {d : ℤ} (hd : 0 < d) :
    (paperInverseLaurentPolynomial p).coeff d = 0 := by
  change (LaurentPolynomial.invert (Polynomial.toLaurent p)).coeff d = _
  rw [LaurentPolynomial.invert_apply, LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨n, hn⟩
  change (n : ℤ) = -d at hn
  omega

variable (I : Ideal R)

/-- The actual native Rees algebra embeds in the paper's extended Rees algebra. -/
def paperNativeReesEmbedding : reesAlgebra I →ₐ[R] PaperIdealExtendedRees I where
  toFun p := ⟨paperInverseLaurentPolynomial (p : Polynomial R), by
    intro d
    by_cases hd : d ≤ 0
    · have he : d = -(((-d).toNat : ℕ) : ℤ) := by omega
      rw [he, paperInverseLaurentPolynomial_coeff_neg_nat, paperIdealPowerFiltration_neg_nat]
      exact p.property (-d).toNat
    · rw [paperInverseLaurentPolynomial_coeff_pos _ (by omega)]
      exact (paperIdealPowerFiltration I d).zero_mem⟩
  map_zero' := Subtype.ext (map_zero paperInverseLaurentPolynomial)
  map_one' := Subtype.ext (map_one paperInverseLaurentPolynomial)
  map_add' p q := Subtype.ext (map_add paperInverseLaurentPolynomial (p : Polynomial R) q)
  map_mul' p q := Subtype.ext (map_mul paperInverseLaurentPolynomial (p : Polynomial R) q)
  commutes' r := Subtype.ext (paperInverseLaurentPolynomial.commutes r)

/-- The embedding retains the exact Laurent representative. -/
theorem paperNativeReesEmbedding_coe (p : reesAlgebra I) :
    (paperNativeReesEmbedding I p : LaurentPolynomial R) =
      paperInverseLaurentPolynomial (p : Polynomial R) := rfl

/-- No native Rees element is lost before specialization. -/
theorem paperNativeReesEmbedding_injective : Function.Injective (paperNativeReesEmbedding I) := by
  intro p q h
  apply Subtype.ext
  apply Polynomial.toLaurent_injective
  apply LaurentPolynomial.invert.injective
  exact congrArg (fun z : PaperIdealExtendedRees I => (z : LaurentPolynomial R)) h

/-- Canonical specialization of native Rees polynomials into the actual associated graded ring. -/
def paperNativeReesSpecialization : reesAlgebra I →ₐ[R] PaperIdealAssociatedGraded I :=
  (Ideal.Quotient.mkₐ R
    (FilteredRees.parameterIdeal (paperIdealPowerFiltration I) (paperIdealPowerFiltration_mono I))).comp
    (paperNativeReesEmbedding I)

/-- A native Rees polynomial vanishes exactly when every coefficient gains one ideal order. -/
theorem paperNativeReesSpecialization_eq_zero_iff_coeff (p : reesAlgebra I) :
    paperNativeReesSpecialization I p = 0 ↔
      ∀ n : ℕ, (p : Polynomial R).coeff n ∈ I ^ (n + 1) := by
  change Ideal.Quotient.mk
    (FilteredRees.parameterIdeal (paperIdealPowerFiltration I) (paperIdealPowerFiltration_mono I))
    (paperNativeReesEmbedding I p) = 0 ↔ _
  rw [paperIdealExtendedRees_specialization_eq_zero_iff]
  constructor
  · intro h n
    have hn := h (-(n : ℤ))
    rw [paperNativeReesEmbedding_coe, paperInverseLaurentPolynomial_coeff_neg_nat] at hn
    have he : (1 - -(n : ℤ)).toNat = n + 1 := by omega
    rwa [he] at hn
  · intro h d
    rw [paperNativeReesEmbedding_coe]
    by_cases hd : d ≤ 0
    · have he : d = -(((-d).toNat : ℕ) : ℤ) := by omega
      rw [he, paperInverseLaurentPolynomial_coeff_neg_nat]
      have hn : (1 - -(((-d).toNat : ℕ) : ℤ)).toNat = (-d).toNat + 1 := by omega
      rw [hn]
      exact h (-d).toNat
    · rw [paperInverseLaurentPolynomial_coeff_pos _ (by omega)]
      exact (I ^ (1 - d).toNat).zero_mem

end

end GaloisForLFunctions.HTGeometry
