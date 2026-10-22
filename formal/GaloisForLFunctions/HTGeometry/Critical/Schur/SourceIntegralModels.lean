import GaloisForLFunctions.HTGeometry.Critical.Schur.SourceCotangent
import GaloisForLFunctions.HTGeometry.Critical.Schur.TailIntegrality
import GaloisForLFunctions.HTGeometry.PolynomialDerivationReciprocal

/-!
# Integral raw and reciprocal models at the actual source Schur place

The raw and reciprocal coordinates of the critical horizon are integral at the Schur divisor, so
both truncations have models over the source Schur valuation ring.  They remain inverse to one
another modulo the horizon, so the Kähler form of `dY = -Y² dX` applies: below the horizon the
differential of a reciprocal coefficient is the rectangular Schur Toeplitz convolution of the
differentials of the raw coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

set_option synthInstance.maxHeartbeats 400000

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- Raw coordinate as an element of the source Schur valuation ring. -/
noncomputable def criticalSourceRawIntegral (i : Fin (m + n)) :
    criticalSchurSourceValuationSubring K hm hn :=
  ⟨criticalSourceRaw K m n i, criticalSourceRaw_mem_sourceValuationSubring K hm hn i⟩

/-- Reciprocal coordinate as an element of the source Schur valuation ring. -/
noncomputable def criticalSourceRecipIntegral (i : Fin (m + n)) :
    criticalSchurSourceValuationSubring K hm hn :=
  ⟨criticalSourceRecip K m n i, criticalSourceRecip_mem_sourceValuationSubring K hm hn i⟩

/-- Integral model of the raw truncation. -/
noncomputable def criticalSourceRawPolynomialIntegral :
    (criticalSchurSourceValuationSubring K hm hn)[X] :=
  ∑ j : Fin (m + n), C (criticalSourceRawIntegral K hm hn j) * X ^ (j : ℕ)

/-- Integral model of the reciprocal truncation. -/
noncomputable def criticalSourceRecipPolynomialIntegral :
    (criticalSchurSourceValuationSubring K hm hn)[X] :=
  ∑ j : Fin (m + n), C (criticalSourceRecipIntegral K hm hn j) * X ^ (j : ℕ)

theorem map_criticalSourceRawPolynomialIntegral :
    (criticalSourceRawPolynomialIntegral K hm hn).map
      (criticalSchurSourceValuationSubring K hm hn).subtype
      = criticalSourceRawPolynomial K m n := by
  rw [criticalSourceRawPolynomialIntegral, criticalSourceRawPolynomial, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rfl

theorem map_criticalSourceRecipPolynomialIntegral :
    (criticalSourceRecipPolynomialIntegral K hm hn).map
      (criticalSchurSourceValuationSubring K hm hn).subtype
      = criticalSourceReciprocalPolynomial K m n := by
  rw [criticalSourceRecipPolynomialIntegral, criticalSourceReciprocalPolynomial,
    Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rfl

theorem X_pow_dvd_criticalSourceIntegral_mul_sub_one :
    (X : (criticalSchurSourceValuationSubring K hm hn)[X]) ^ (m + n) ∣
      criticalSourceRawPolynomialIntegral K hm hn *
        criticalSourceRecipPolynomialIntegral K hm hn - 1 := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  have hinj : Function.Injective
      (criticalSchurSourceValuationSubring K hm hn).subtype := Subtype.val_injective
  apply hinj
  have hfield := X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n
  rw [Polynomial.X_pow_dvd_iff] at hfield
  have := hfield k hk
  rw [← map_criticalSourceRawPolynomialIntegral K hm hn,
    ← map_criticalSourceRecipPolynomialIntegral K hm hn, ← Polynomial.map_mul,
    ← Polynomial.map_one (f := (criticalSchurSourceValuationSubring K hm hn).subtype),
    ← Polynomial.map_sub, Polynomial.coeff_map] at this
  simpa using this

theorem criticalSourceRawPolynomialIntegral_coeff (k : ℕ) (hk : k < m + n) :
    (criticalSourceRawPolynomialIntegral K hm hn).coeff k
      = criticalSourceRawIntegral K hm hn ⟨k, hk⟩ := by
  classical
  rw [criticalSourceRawPolynomialIntegral, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨k, hk⟩ : Fin (m + n))]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ _) h

theorem criticalSourceRecipPolynomialIntegral_coeff (k : ℕ) (hk : k < m + n) :
    (criticalSourceRecipPolynomialIntegral K hm hn).coeff k
      = criticalSourceRecipIntegral K hm hn ⟨k, hk⟩ := by
  classical
  rw [criticalSourceRecipPolynomialIntegral, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨k, hk⟩ : Fin (m + n))]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **The Kähler form of `dY = -Y² dX` at the actual source Schur place.** -/
theorem D_criticalSourceRecipPolynomialIntegral_coeff (l : ℕ) (hl : l < m + n) :
    KaehlerDifferential.D K (criticalSchurSourceValuationSubring K hm hn)
        ((criticalSourceRecipPolynomialIntegral K hm hn).coeff l)
      = -∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (A := ℕ) l : Finset (ℕ × ℕ)),
          (criticalSourceRecipPolynomialIntegral K hm hn *
              criticalSourceRecipPolynomialIntegral K hm hn).coeff x.1 •
            KaehlerDifferential.D K (criticalSchurSourceValuationSubring K hm hn)
              ((criticalSourceRawPolynomialIntegral K hm hn).coeff x.2) :=
  polyD_reciprocal _ (X_pow_dvd_criticalSourceIntegral_mul_sub_one K hm hn) hl

end

end GaloisForLFunctions.HTGeometry
