import GaloisForLFunctions.HTGeometry.GenericJetAlgebra
import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre

/-!
# Polynomial truncations of the generic inverse jet

The coefficient families defined recursively in `GenericJetAlgebra` form inverse polynomials modulo
the jet horizon.  This packages the recursion as the divisibility statement used by the actual
critical function-field fibre.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- Polynomial containing every generic raw coefficient through order `N`. -/
noncomputable def genericRawPolynomial
    (K : Type*) [Field K] (N : ℕ) : (genericJetAlgebra K N)[X] :=
  ∑ j : Fin (N + 1), C (genericRaw K N (j : ℕ)) * X ^ (j : ℕ)

/-- Polynomial containing every generic reciprocal coefficient through order `N`. -/
noncomputable def genericRecipPolynomial
    (K : Type*) [Field K] (N : ℕ) : (genericJetAlgebra K N)[X] :=
  ∑ j : Fin (N + 1), C (genericRecip K N (j : ℕ)) * X ^ (j : ℕ)

theorem genericRawPolynomial_coeff
    (K : Type*) [Field K] (N k : ℕ) (hk : k < N + 1) :
    (genericRawPolynomial K N).coeff k = genericRaw K N k := by
  classical
  rw [genericRawPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨k, hk⟩ : Fin (N + 1))]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ _) h

theorem genericRecipPolynomial_coeff
    (K : Type*) [Field K] (N k : ℕ) (hk : k < N + 1) :
    (genericRecipPolynomial K N).coeff k = genericRecip K N k := by
  classical
  rw [genericRecipPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨k, hk⟩ : Fin (N + 1))]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ _) h

/-- Every coefficient below the horizon of the generic raw/reciprocal product is the corresponding
coefficient of `1`. -/
theorem genericRawPolynomial_mul_genericRecipPolynomial_coeff
    (K : Type*) [Field K] (N k : ℕ) (hk : k < N + 1) :
    (genericRawPolynomial K N * genericRecipPolynomial K N).coeff k =
      (1 : (genericJetAlgebra K N)[X]).coeff k := by
  classical
  rcases k with _ | k
  · rw [Polynomial.mul_coeff_zero, genericRawPolynomial_coeff K N 0 (by omega),
      genericRecipPolynomial_coeff K N 0 (by omega), genericRecip,
      genericRaw_zero_mul_inv, Polynomial.coeff_one_zero]
  · rw [coeff_mul_range, Finset.sum_range_succ']
    have hraw0 : (genericRawPolynomial K N).coeff 0 = genericRaw K N 0 :=
      genericRawPolynomial_coeff K N 0 (by omega)
    have hrecipSucc : (genericRecipPolynomial K N).coeff (k + 1) =
        genericRecip K N (k + 1) :=
      genericRecipPolynomial_coeff K N (k + 1) (by omega)
    rw [hraw0, Nat.sub_zero, hrecipSucc]
    have hsum :
        (∑ i ∈ Finset.range (k + 1),
            (genericRawPolynomial K N).coeff (i + 1) *
              (genericRecipPolynomial K N).coeff (k + 1 - (i + 1))) =
          ∑ i ∈ Finset.range (k + 1),
            genericRaw K N (i + 1) * genericRecip K N (k - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [genericRawPolynomial_coeff K N (i + 1) (by omega),
        genericRecipPolynomial_coeff K N (k + 1 - (i + 1)) (by omega)]
      congr 2
      omega
    rw [hsum, genericRecip]
    have hmul := genericRaw_zero_mul_inv K N
    have hcancel :
        genericRaw K N 0 *
            (-genericInv K N * ∑ i ∈ Finset.range (k + 1),
              genericRaw K N (i + 1) * genericRecip K N (k - i)) =
          -(∑ i ∈ Finset.range (k + 1),
              genericRaw K N (i + 1) * genericRecip K N (k - i)) := by
      calc
        _ = -(genericRaw K N 0 * genericInv K N) *
            ∑ i ∈ Finset.range (k + 1),
              genericRaw K N (i + 1) * genericRecip K N (k - i) := by ring
        _ = _ := by rw [hmul]; ring
    rw [hcancel]
    rw [add_neg_cancel, Polynomial.coeff_one, if_neg (by omega)]

/-- The generic raw and reciprocal truncations multiply to one modulo the horizon. -/
theorem X_pow_dvd_genericRawPolynomial_mul_genericRecipPolynomial_sub_one
    (K : Type*) [Field K] (N : ℕ) :
    (X : (genericJetAlgebra K N)[X]) ^ (N + 1) ∣
      genericRawPolynomial K N * genericRecipPolynomial K N - 1 := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [Polynomial.coeff_sub,
    genericRawPolynomial_mul_genericRecipPolynomial_coeff K N k hk, sub_self]

end GaloisForLFunctions.HTGeometry
