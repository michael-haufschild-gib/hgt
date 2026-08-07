import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromy
import GaloisForLFunctions.HTGeometry.GenericJetInversePolynomial

/-!
# Geometric sheets as actual critical-fibre points

Every embedding of the critical source field into its normal closure sends the low raw and
reciprocal coefficient blocks to a compatible critical factorization.  The resulting map from
geometric sheets to the critical fibre is injective because the raw source coordinates generate
the source field over the observation field.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- Raw observation coordinate as an element of the actual observation field. -/
noncomputable def criticalObservationRaw
    (K : Type*) [Field K] (m n : ℕ) (i : Fin n) :
    criticalObservationField K m n :=
  ⟨criticalAmbientRaw K m n (m + (i : ℕ)),
    IntermediateField.subset_adjoin K _ ⟨Sum.inl i, rfl⟩⟩

/-- Reciprocal observation coordinate as an element of the actual observation field. -/
noncomputable def criticalObservationRecip
    (K : Type*) [Field K] (m n : ℕ) (j : Fin m) :
    criticalObservationField K m n :=
  ⟨criticalAmbientRecip K m n (n + (j : ℕ)),
    IntermediateField.subset_adjoin K _ ⟨Sum.inr j, rfl⟩⟩

/-- Raw observed tail over the actual observation field. -/
noncomputable def criticalObservationRawTail
    (K : Type*) [Field K] (m n : ℕ) :
    (criticalObservationField K m n)[X] :=
  ∑ i : Fin n, C (criticalObservationRaw K m n i) * X ^ (m + (i : ℕ))

/-- Reciprocal observed tail over the actual observation field. -/
noncomputable def criticalObservationReciprocalTail
    (K : Type*) [Field K] (m n : ℕ) :
    (criticalObservationField K m n)[X] :=
  ∑ j : Fin m, C (criticalObservationRecip K m n j) * X ^ (n + (j : ℕ))

theorem X_pow_dvd_criticalObservationRawTail
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (criticalObservationField K m n)[X]) ^ m ∣
      criticalObservationRawTail K m n := by
  classical
  rw [criticalObservationRawTail]
  refine Finset.dvd_sum fun i _ => ?_
  refine ⟨C (criticalObservationRaw K m n i) * X ^ (i : ℕ), ?_⟩
  rw [pow_add]
  ring

theorem X_pow_dvd_criticalObservationReciprocalTail
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (criticalObservationField K m n)[X]) ^ n ∣
      criticalObservationReciprocalTail K m n := by
  classical
  rw [criticalObservationReciprocalTail]
  refine Finset.dvd_sum fun j _ => ?_
  refine ⟨C (criticalObservationRecip K m n j) * X ^ (j : ℕ), ?_⟩
  rw [pow_add]
  ring

/-- Reciprocal coefficient through the critical horizon, as an element of the source field. -/
noncomputable def criticalSourceRecip
    (K : Type*) [Field K] (m n : ℕ) (j : Fin (m + n)) :
    criticalSourceField K m n :=
  ⟨criticalAmbientRecip K m n (j : ℕ),
    criticalAmbientRecip_mem_criticalSourceField K j.isLt⟩

/-- Low raw block in the actual source field. -/
noncomputable def criticalSourceRawLow
    (K : Type*) [Field K] (m n : ℕ) : (criticalSourceField K m n)[X] :=
  lowPolynomial (fun i : Fin m =>
    criticalSourceRaw K m n ⟨i, lt_trans i.isLt (by omega)⟩)

/-- Low reciprocal block in the actual source field. -/
noncomputable def criticalSourceReciprocalLow
    (K : Type*) [Field K] (m n : ℕ) : (criticalSourceField K m n)[X] :=
  lowPolynomial (fun j : Fin n =>
    criticalSourceRecip K m n ⟨j, lt_trans j.isLt (by omega)⟩)

/-- Full raw polynomial through order `m+n-1` in the actual source field. -/
noncomputable def criticalSourceRawPolynomial
    (K : Type*) [Field K] (m n : ℕ) : (criticalSourceField K m n)[X] :=
  ∑ j : Fin (m + n), C (criticalSourceRaw K m n j) * X ^ (j : ℕ)

/-- Full reciprocal polynomial through order `m+n-1` in the actual source field. -/
noncomputable def criticalSourceReciprocalPolynomial
    (K : Type*) [Field K] (m n : ℕ) : (criticalSourceField K m n)[X] :=
  ∑ j : Fin (m + n), C (criticalSourceRecip K m n j) * X ^ (j : ℕ)

theorem criticalSourceRawPolynomial_coeff
    (K : Type*) [Field K] (m n k : ℕ) (hk : k < m + n) :
    (criticalSourceRawPolynomial K m n).coeff k =
      criticalSourceRaw K m n ⟨k, hk⟩ := by
  classical
  rw [criticalSourceRawPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨k, hk⟩ : Fin (m + n))]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ _) h

theorem criticalSourceReciprocalPolynomial_coeff
    (K : Type*) [Field K] (m n k : ℕ) (hk : k < m + n) :
    (criticalSourceReciprocalPolynomial K m n).coeff k =
      criticalSourceRecip K m n ⟨k, hk⟩ := by
  classical
  rw [criticalSourceReciprocalPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨k, hk⟩ : Fin (m + n))]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hj (Fin.ext h.symm)
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The full source raw polynomial splits into its low block and observed tail. -/
theorem criticalSourceRawPolynomial_eq_low_add_tail
    (K : Type*) [Field K] (m n : ℕ) :
    criticalSourceRawPolynomial K m n = criticalSourceRawLow K m n +
      (criticalObservationRawTail K m n).map
        (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < m + n
  · rw [criticalSourceRawPolynomial_coeff K m n k hk, Polynomial.coeff_add,
      Polynomial.coeff_map]
    by_cases hkm : k < m
    · have htail : (criticalObservationRawTail K m n).coeff k = 0 := by
        rw [criticalObservationRawTail, Polynomial.finsetSum_coeff]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
        omega
      rw [criticalSourceRawLow, lowPolynomial_coeff, dif_pos hkm, htail, map_zero, add_zero]
      apply Subtype.ext
      rfl
    · have hmn : m ≤ k := Nat.le_of_not_gt hkm
      have hkn : k - m < n := by omega
      let i : Fin n := ⟨k - m, hkn⟩
      have htail : (criticalObservationRawTail K m n).coeff k =
          criticalObservationRaw K m n i := by
        rw [criticalObservationRawTail, Polynomial.finsetSum_coeff,
          Finset.sum_eq_single i]
        · simp [i, Nat.add_sub_of_le hmn]
        · intro j _ hji
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
          exact fun h => hji (Fin.ext (by omega))
        · exact fun h => absurd (Finset.mem_univ _) h
      rw [criticalSourceRawLow, lowPolynomial_coeff, dif_neg hkm, htail, zero_add]
      apply Subtype.ext
      rfl
  · have hge : m + n ≤ k := Nat.le_of_not_gt hk
    rw [Polynomial.coeff_add, Polynomial.coeff_map]
    have hfull : (criticalSourceRawPolynomial K m n).coeff k = 0 := by
      rw [criticalSourceRawPolynomial, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      omega
    have hlow : (criticalSourceRawLow K m n).coeff k = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero _ m).mp
        (lowPolynomial_degree_lt _) k (by omega)
    have htail : (criticalObservationRawTail K m n).coeff k = 0 := by
      rw [criticalObservationRawTail, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      omega
    rw [hfull, hlow, htail, map_zero, add_zero]

/-- The full source reciprocal polynomial splits into its low block and observed tail. -/
theorem criticalSourceReciprocalPolynomial_eq_low_add_tail
    (K : Type*) [Field K] (m n : ℕ) :
    criticalSourceReciprocalPolynomial K m n = criticalSourceReciprocalLow K m n +
      (criticalObservationReciprocalTail K m n).map
        (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)) := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k < m + n
  · rw [criticalSourceReciprocalPolynomial_coeff K m n k hk, Polynomial.coeff_add,
      Polynomial.coeff_map]
    by_cases hkn : k < n
    · have htail : (criticalObservationReciprocalTail K m n).coeff k = 0 := by
        rw [criticalObservationReciprocalTail, Polynomial.finsetSum_coeff]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
        omega
      rw [criticalSourceReciprocalLow, lowPolynomial_coeff, dif_pos hkn,
        htail, map_zero, add_zero]
      apply Subtype.ext
      rfl
    · have hnm : n ≤ k := Nat.le_of_not_gt hkn
      have hkm : k - n < m := by omega
      let j : Fin m := ⟨k - n, hkm⟩
      have htail : (criticalObservationReciprocalTail K m n).coeff k =
          criticalObservationRecip K m n j := by
        rw [criticalObservationReciprocalTail, Polynomial.finsetSum_coeff,
          Finset.sum_eq_single j]
        · simp [j, Nat.add_sub_of_le hnm]
        · intro i _ hij
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
          exact fun h => hij (Fin.ext (by omega))
        · exact fun h => absurd (Finset.mem_univ _) h
      rw [criticalSourceReciprocalLow, lowPolynomial_coeff, dif_neg hkn, htail, zero_add]
      apply Subtype.ext
      rfl
  · have hge : m + n ≤ k := Nat.le_of_not_gt hk
    rw [Polynomial.coeff_add, Polynomial.coeff_map]
    have hfull : (criticalSourceReciprocalPolynomial K m n).coeff k = 0 := by
      rw [criticalSourceReciprocalPolynomial, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      omega
    have hlow : (criticalSourceReciprocalLow K m n).coeff k = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero _ n).mp
        (lowPolynomial_degree_lt _) k (by omega)
    have htail : (criticalObservationReciprocalTail K m n).coeff k = 0 := by
      rw [criticalObservationReciprocalTail, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      omega
    rw [hfull, hlow, htail, map_zero, add_zero]

/-- The actual source raw and reciprocal truncations are inverse modulo the critical horizon. -/
theorem X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣
      criticalSourceRawPolynomial K m n *
        criticalSourceReciprocalPolynomial K m n - 1 := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  apply Subtype.ext
  have hgeneric := genericRawPolynomial_mul_genericRecipPolynomial_coeff
    K (m + n) k (by omega)
  have hmapped := congrArg (genericJetFieldMap K (m + n)) hgeneric
  rw [map_sub]
  simpa only [Polynomial.coeff_sub, Polynomial.coeff_one,
    criticalSourceRawPolynomial, criticalSourceReciprocalPolynomial,
    Polynomial.coeff_mul, map_zero, Subtype.coe_zero] using hmapped

/-- A geometric sheet evaluated on the low coefficient blocks is an actual critical-fibre point
over the normal closure. -/
noncomputable def criticalGeometricSheetToFibre
    (K : Type*) [Field K] (m n : ℕ) :
    criticalGeometricSheet K m n →
      criticalFibre (criticalNormalClosure K m n) m n
        ((criticalObservationRawTail K m n).map
          (algebraMap (criticalObservationField K m n) (criticalNormalClosure K m n)))
        ((criticalObservationReciprocalTail K m n).map
          (algebraMap (criticalObservationField K m n) (criticalNormalClosure K m n))) := by
  intro σ
  let A := (criticalSourceRawLow K m n).map σ
  let B := (criticalSourceReciprocalLow K m n).map σ
  refine ⟨(A, B), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _)
  · exact lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _)
  · apply (dvd_criticalLowProduct_sub_one_iff_mul_sub_one
      (Polynomial.map_dvd _ (X_pow_dvd_criticalObservationRawTail K m n))
      (Polynomial.map_dvd _ (X_pow_dvd_criticalObservationReciprocalTail K m n)) A B).2
    have h := Polynomial.map_dvd σ
      (X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n)
    rw [criticalSourceRawPolynomial_eq_low_add_tail,
      criticalSourceReciprocalPolynomial_eq_low_add_tail] at h
    simpa only [A, B, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_one, Polynomial.map_map, RingHomCompTriple.comp_eq,
      σ.commutes] using h

/-- Distinct geometric sheets give distinct compatible critical states. -/
theorem criticalGeometricSheetToFibre_injective
    (K : Type*) [Field K] (m n : ℕ) :
    Function.Injective (criticalGeometricSheetToFibre K m n) := by
  intro σ τ hστ
  have hA : (criticalSourceRawLow K m n).map σ =
      (criticalSourceRawLow K m n).map τ :=
    congrArg (fun p => p.1.1) hστ
  apply AlgHom.ext
  intro x
  have hx : x ∈ IntermediateField.adjoin (criticalObservationField K m n)
      (Set.range (criticalSourceRaw K m n)) := by
    rw [criticalSourceRaw_adjoin_eq_top K m n]
    trivial
  exact IntermediateField.adjoin_induction
    (criticalObservationField K m n)
    (p := fun z _ => σ z = τ z)
    (fun z hz => by
      obtain ⟨j, rfl⟩ := hz
      by_cases hj : (j : ℕ) < m
      · have hc := congrArg (fun P : (criticalNormalClosure K m n)[X] =>
            P.coeff (j : ℕ)) hA
        simpa [criticalSourceRawLow, lowPolynomial_coeff, hj] using hc
      · have hjm : m ≤ (j : ℕ) := Nat.le_of_not_gt hj
        have hjn : (j : ℕ) - m < n := by omega
        let i : Fin n := ⟨(j : ℕ) - m, hjn⟩
        have hcoord : criticalSourceRaw K m n j =
            algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
              (criticalObservationRaw K m n i) := by
          apply Subtype.ext
          simp [criticalSourceRaw, criticalObservationRaw, i, Nat.add_sub_of_le hjm]
        rw [hcoord, σ.commutes, τ.commutes])
    (fun z => by rw [σ.commutes, τ.commutes])
    (fun _ _ _ _ hz hw => by rw [map_add, map_add, hz, hw])
    (fun _ _ hz => by rw [map_inv₀, map_inv₀, hz])
    (fun _ _ _ _ hz hw => by rw [map_mul, map_mul, hz, hw]) hx

end

end GaloisForLFunctions.HTGeometry
