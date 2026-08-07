import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromy
import GaloisForLFunctions.HTGeometry.GenericJetInversePolynomial
import GaloisForLFunctions.HTGeometry.LaurentCriticalFibreIntegrality

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

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

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
    criticalSourceRaw K m n ⟨i, lt_of_lt_of_le i.isLt (Nat.le_add_right m n)⟩)

/-- Low reciprocal block in the actual source field. -/
noncomputable def criticalSourceReciprocalLow
    (K : Type*) [Field K] (m n : ℕ) : (criticalSourceField K m n)[X] :=
  lowPolynomial (fun j : Fin n =>
    criticalSourceRecip K m n ⟨j, lt_of_lt_of_le j.isLt (Nat.le_add_left n m)⟩)

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
          intro heq
          apply hji
          apply Fin.ext
          dsimp [i]
          omega
        · exact fun h => absurd (Finset.mem_univ _) h
      rw [criticalSourceRawLow, lowPolynomial_coeff, dif_neg hkm, htail, zero_add]
      apply Subtype.ext
      change criticalAmbientRaw K m n k =
        criticalAmbientRaw K m n (m + (i : ℕ))
      congr 1
      dsimp [i]
      omega
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
          intro heq
          apply hij
          apply Fin.ext
          dsimp [j]
          omega
        · exact fun h => absurd (Finset.mem_univ _) h
      rw [criticalSourceReciprocalLow, lowPolynomial_coeff, dif_neg hkn, htail, zero_add]
      apply Subtype.ext
      change criticalAmbientRecip K m n k =
        criticalAmbientRecip K m n (n + (j : ℕ))
      congr 1
      dsimp [j]
      omega
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
  have hgeneric := genericRawPolynomial_mul_genericRecipPolynomial_coeff
    K (m + n) k (by omega)
  have hmapped := congrArg (genericJetFieldMap K (m + n)) hgeneric
  have hprod :
      genericJetFieldMap K (m + n)
          ((genericRawPolynomial K (m + n) *
            genericRecipPolynomial K (m + n)).coeff k) =
        (((criticalSourceRawPolynomial K m n *
          criticalSourceReciprocalPolynomial K m n).coeff k :
            criticalSourceField K m n) : genericJetField K (m + n)) := by
    calc
      _ = ∑ i ∈ Finset.range (k + 1),
          genericJetFieldMap K (m + n)
            ((genericRawPolynomial K (m + n)).coeff i *
              (genericRecipPolynomial K (m + n)).coeff (k - i)) := by
            rw [coeff_mul_range, map_sum]
      _ = ∑ i ∈ Finset.range (k + 1),
          (((criticalSourceRawPolynomial K m n).coeff i :
            criticalSourceField K m n) : genericJetField K (m + n)) *
          (((criticalSourceReciprocalPolynomial K m n).coeff (k - i) :
            criticalSourceField K m n) : genericJetField K (m + n)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi' := Finset.mem_range.1 hi
            rw [map_mul,
              genericRawPolynomial_coeff K (m + n) i (by omega),
              genericRecipPolynomial_coeff K (m + n) (k - i) (by omega),
              criticalSourceRawPolynomial_coeff K m n i (by omega),
              criticalSourceReciprocalPolynomial_coeff K m n (k - i) (by omega)]
            rfl
      _ = _ := by
        rw [coeff_mul_range]
        change (∑ i ∈ Finset.range (k + 1),
            (criticalSourceField K m n).val
              ((criticalSourceRawPolynomial K m n).coeff i) *
            (criticalSourceField K m n).val
              ((criticalSourceReciprocalPolynomial K m n).coeff (k - i))) =
          (criticalSourceField K m n).val
            (∑ i ∈ Finset.range (k + 1),
              (criticalSourceRawPolynomial K m n).coeff i *
              (criticalSourceReciprocalPolynomial K m n).coeff (k - i))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul]
  have hone :
      genericJetFieldMap K (m + n)
          ((1 : (genericJetAlgebra K (m + n))[X]).coeff k) =
        (((1 : (criticalSourceField K m n)[X]).coeff k :
            criticalSourceField K m n) : genericJetField K (m + n)) := by
    rcases k with _ | k
    · simp [Polynomial.coeff_one_zero]
    · have hg : (1 : (genericJetAlgebra K (m + n))[X]).coeff (k + 1) = 0 := by
        rw [Polynomial.coeff_one, if_neg (by omega)]
      have hs : (1 : (criticalSourceField K m n)[X]).coeff (k + 1) = 0 := by
        rw [Polynomial.coeff_one, if_neg (by omega)]
      rw [hg, hs, map_zero]
      rfl
  rw [Polynomial.coeff_sub]
  apply sub_eq_zero.mpr
  apply Subtype.ext
  rw [← hprod, ← hone]
  exact hmapped

/-- A geometric sheet followed by the normal-closure inclusion into the chosen algebraic closure. -/
noncomputable def criticalGeometricSheetAmbient
    (K : Type*) [Field K] (m n : ℕ) (σ : criticalGeometricSheet K m n) :
    criticalSourceField K m n →ₐ[criticalObservationField K m n]
      criticalSourceAlgebraicClosure K m n :=
  (criticalNormalClosure K m n).val.comp σ

/-- Explicit observation-field inclusion into the chosen source algebraic closure. -/
noncomputable def criticalObservationSourceAlgebraicClosureMap
    (K : Type*) [Field K] (m n : ℕ) :
    criticalObservationField K m n →+* criticalSourceAlgebraicClosure K m n :=
  (algebraMap (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)).comp
    (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))

theorem X_pow_dvd_criticalObservationRawTail_map_algebraicClosure
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (criticalSourceAlgebraicClosure K m n)[X]) ^ m ∣
      (criticalObservationRawTail K m n).map
        (criticalObservationSourceAlgebraicClosureMap K m n) :=
  by
    simpa using Polynomial.map_dvd
      (criticalObservationSourceAlgebraicClosureMap K m n)
      (X_pow_dvd_criticalObservationRawTail K m n)

theorem X_pow_dvd_criticalObservationReciprocalTail_map_algebraicClosure
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (criticalSourceAlgebraicClosure K m n)[X]) ^ n ∣
      (criticalObservationReciprocalTail K m n).map
        (criticalObservationSourceAlgebraicClosureMap K m n) :=
  by
    simpa using Polynomial.map_dvd
      (criticalObservationSourceAlgebraicClosureMap K m n)
      (X_pow_dvd_criticalObservationReciprocalTail K m n)

/-- Mapping the actual generic inverse identity along a geometric sheet gives inverse coefficient
blocks in the chosen algebraic closure. -/
theorem criticalGeometricSheet_mapped_inverse
    (K : Type*) [Field K] (m n : ℕ) (σ : criticalGeometricSheet K m n) :
    (X : (criticalSourceAlgebraicClosure K m n)[X]) ^ (m + n) ∣
      ((criticalSourceRawLow K m n).map
          (criticalGeometricSheetAmbient K m n σ).toRingHom +
        (criticalObservationRawTail K m n).map
          (criticalObservationSourceAlgebraicClosureMap K m n)) *
      ((criticalSourceReciprocalLow K m n).map
          (criticalGeometricSheetAmbient K m n σ).toRingHom +
        (criticalObservationReciprocalTail K m n).map
          (criticalObservationSourceAlgebraicClosureMap K m n)) - 1 := by
  let ρ := criticalGeometricSheetAmbient K m n σ
  have h := Polynomial.map_dvd ρ.toRingHom
    (X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n)
  rw [criticalSourceRawPolynomial_eq_low_add_tail,
    criticalSourceReciprocalPolynomial_eq_low_add_tail] at h
  have hcomp : ρ.toRingHom.comp
      (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)) =
    criticalObservationSourceAlgebraicClosureMap K m n := by
    ext z
    exact ρ.commutes z
  simpa only [ρ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_map, Polynomial.map_pow, Polynomial.map_X,
    hcomp] using h

/-- A geometric sheet evaluated on the low coefficient blocks is an actual critical-fibre point
over the chosen source algebraic closure. -/
noncomputable def criticalGeometricSheetToFibre
    (K : Type*) [Field K] (m n : ℕ) :
    criticalGeometricSheet K m n →
      criticalFibre (criticalSourceAlgebraicClosure K m n) m n
        ((criticalObservationRawTail K m n).map
          (criticalObservationSourceAlgebraicClosureMap K m n))
        ((criticalObservationReciprocalTail K m n).map
          (criticalObservationSourceAlgebraicClosureMap K m n)) := by
  intro σ
  let ρ := criticalGeometricSheetAmbient K m n σ
  let A := (criticalSourceRawLow K m n).map ρ.toRingHom
  let B := (criticalSourceReciprocalLow K m n).map ρ.toRingHom
  refine ⟨(A, B), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _)
  · exact lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _)
  · apply (dvd_criticalLowProduct_sub_one_iff_mul_sub_one
      (X_pow_dvd_criticalObservationRawTail_map_algebraicClosure K m n)
      (X_pow_dvd_criticalObservationReciprocalTail_map_algebraicClosure K m n) A B).2
    exact criticalGeometricSheet_mapped_inverse K m n σ

/-- Distinct geometric sheets give distinct compatible critical states. -/
theorem criticalGeometricSheetToFibre_injective
    (K : Type*) [Field K] (m n : ℕ) :
    Function.Injective (criticalGeometricSheetToFibre K m n) := by
  intro σ τ hστ
  let ρσ := criticalGeometricSheetAmbient K m n σ
  let ρτ := criticalGeometricSheetAmbient K m n τ
  have hA : (criticalSourceRawLow K m n).map ρσ.toRingHom =
      (criticalSourceRawLow K m n).map ρτ.toRingHom :=
    congrArg (fun p => p.1.1) hστ
  have hρ : ρσ = ρτ := by
    apply AlgHom.ext
    intro x
    have hx : x ∈ IntermediateField.adjoin (criticalObservationField K m n)
        (Set.range (criticalSourceRaw K m n)) := by
      rw [criticalSourceRaw_adjoin_eq_top K m n]
      trivial
    exact IntermediateField.adjoin_induction
      (criticalObservationField K m n)
      (p := fun z _ => ρσ z = ρτ z)
      (fun z hz => by
        obtain ⟨j, rfl⟩ := hz
        by_cases hj : (j : ℕ) < m
        · have hc := congrArg (fun P : (criticalSourceAlgebraicClosure K m n)[X] =>
              P.coeff (j : ℕ)) hA
          simpa [criticalSourceRawLow, lowPolynomial_coeff, hj] using hc
        · have hjm : m ≤ (j : ℕ) := Nat.le_of_not_gt hj
          have hjn : (j : ℕ) - m < n := by omega
          let i : Fin n := ⟨(j : ℕ) - m, hjn⟩
          have hcoord : criticalSourceRaw K m n j =
              algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
                (criticalObservationRaw K m n i) := by
            apply Subtype.ext
            change criticalAmbientRaw K m n (j : ℕ) =
              criticalAmbientRaw K m n (m + (i : ℕ))
            congr 1
            dsimp [i]
            omega
          rw [hcoord, ρσ.commutes, ρτ.commutes])
      (fun z => by rw [ρσ.commutes, ρτ.commutes])
      (fun _ _ _ _ hz hw => by rw [map_add, map_add, hz, hw])
      (fun _ _ hz => by rw [map_inv₀, map_inv₀, hz])
      (fun _ _ _ _ hz hw => by rw [map_mul, map_mul, hz, hw]) hx
  apply AlgHom.ext
  intro x
  apply (criticalNormalClosure K m n).val.injective
  exact DFunLike.congr_fun hρ x

end

end GaloisForLFunctions.HTGeometry
