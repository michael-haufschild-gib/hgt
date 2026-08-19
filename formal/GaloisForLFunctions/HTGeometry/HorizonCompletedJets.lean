import GaloisForLFunctions.HTGeometry.HorizonPresentationDifferential
import GaloisForLFunctions.HTGeometry.TruncatedToeplitz

/-!
# The completed jets of the critical fibre presentation

Assembling the unknown low coefficients with the observed tails gives the two completed jets over
the presentation ring, and the truncated compatibility relations are exactly the low coefficients of
their inversion error:

```text
horizonRawJet, horizonRecipJet
horizonRawJet_coeff, horizonRecipJet_coeff     coeff i is the corresponding presentation coefficient
horizonRelation_eq_coeff
    ** horizonRelation k = (rawJet * recipJet - 1).coeff k **
```

This is the form the Toeplitz calculus consumes: in the fibre algebra the inversion error vanishes
below the horizon, so `TruncatedToeplitz.toeplitz_mul_toeplitz_of_inverse` makes the Toeplitz matrix
of the reciprocal jet the inverse of that of the raw jet — which is what turns the Sylvester block
of the presentation differential into a block with an identity corner.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial MvPolynomial

variable (A : Type*) [CommRing A] (m n : ℕ) (P Q : A[X])

/-- The completed raw jet of the critical fibre, over the presentation ring. -/
noncomputable def horizonRawJet : (MvPolynomial (Fin (m + n)) A)[X] :=
  (∑ i ∈ Finset.range m,
      Polynomial.C (horizonRawCoeff A m n P i - MvPolynomial.C (P.coeff i)) * Polynomial.X ^ i)
    + P.map (MvPolynomial.C : A →+* MvPolynomial (Fin (m + n)) A)

/-- The completed reciprocal jet of the critical fibre. -/
noncomputable def horizonRecipJet : (MvPolynomial (Fin (m + n)) A)[X] :=
  (∑ j ∈ Finset.range n,
      Polynomial.C (horizonRecipCoeff A m n Q j - MvPolynomial.C (Q.coeff j)) * Polynomial.X ^ j)
    + Q.map (MvPolynomial.C : A →+* MvPolynomial (Fin (m + n)) A)

theorem horizonRawJet_coeff (i : ℕ) :
    (horizonRawJet A m n P).coeff i = horizonRawCoeff A m n P i := by
  classical
  rw [horizonRawJet, Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  have hsum : ∑ k ∈ Finset.range m,
      (Polynomial.C (horizonRawCoeff A m n P k - MvPolynomial.C (P.coeff k)) *
        Polynomial.X ^ k).coeff i
      = if i < m then horizonRawCoeff A m n P i - MvPolynomial.C (P.coeff i) else 0 := by
    have hterm : ∀ k ∈ Finset.range m,
        (Polynomial.C (horizonRawCoeff A m n P k - MvPolynomial.C (P.coeff k)) *
          Polynomial.X ^ k).coeff i
        = if k = i then horizonRawCoeff A m n P i - MvPolynomial.C (P.coeff i) else 0 := by
      intro k _
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hk : k = i
      · subst hk
        rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg (fun hc => hk hc.symm), if_neg hk, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range m) i]
    by_cases hi : i < m
    · rw [if_pos (Finset.mem_range.mpr hi), if_pos hi]
    · rw [if_neg (by simpa [Finset.mem_range] using hi), if_neg hi]
  rw [hsum, horizonRawCoeff]
  by_cases hi : i < m
  · rw [if_pos hi, dif_pos hi]
    ring
  · rw [if_neg hi, dif_neg hi]
    ring

theorem horizonRecipJet_coeff (j : ℕ) :
    (horizonRecipJet A m n Q).coeff j = horizonRecipCoeff A m n Q j := by
  classical
  rw [horizonRecipJet, Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  have hsum : ∑ k ∈ Finset.range n,
      (Polynomial.C (horizonRecipCoeff A m n Q k - MvPolynomial.C (Q.coeff k)) *
        Polynomial.X ^ k).coeff j
      = if j < n then horizonRecipCoeff A m n Q j - MvPolynomial.C (Q.coeff j) else 0 := by
    have hterm : ∀ k ∈ Finset.range n,
        (Polynomial.C (horizonRecipCoeff A m n Q k - MvPolynomial.C (Q.coeff k)) *
          Polynomial.X ^ k).coeff j
        = if k = j then horizonRecipCoeff A m n Q j - MvPolynomial.C (Q.coeff j) else 0 := by
      intro k _
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hk : k = j
      · subst hk
        rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg (fun hc => hk hc.symm), if_neg hk, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range n) j]
    by_cases hj : j < n
    · rw [if_pos (Finset.mem_range.mpr hj), if_pos hj]
    · rw [if_neg (by simpa [Finset.mem_range] using hj), if_neg hj]
  rw [hsum, horizonRecipCoeff]
  by_cases hj : j < n
  · rw [if_pos hj, dif_pos hj]
    ring
  · rw [if_neg hj, dif_neg hj]
    ring

/-- **The relations are the low coefficients of the inversion error.** -/
theorem horizonRelation_eq_coeff (k : Fin (m + n)) :
    horizonRelation A m n P Q k
      = (horizonRawJet A m n P * horizonRecipJet A m n Q - 1).coeff (k : ℕ) := by
  classical
  rw [horizonRelation, Polynomial.coeff_sub, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Polynomial.coeff_one]
  refine congrArg (fun t => t - (if (k : ℕ) = 0 then (1 : MvPolynomial (Fin (m + n)) A) else 0)) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [horizonRawJet_coeff, horizonRecipJet_coeff]

end

end GaloisForLFunctions.HTGeometry
