import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalFibre
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.ValuationCriticalFibreIntegrality

/-!
# Reduction of geometric sheets at the common-scale normal-closure place

The common-scale place of the actual critical normal closure makes every observed tail integral.
This file identifies their reductions with the two pure tails and uses projective-boundary
integrality to reduce every actual geometric sheet without introducing an abstract valued-field
extension or a ramification hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped LaurentSeries

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

private abbrev ArcBaseRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcBaseRing K m n hm hn

private abbrev ArcIntegralClosure
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcIntegralClosure K m n hm hn

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

theorem criticalObservationRaw_mem_arcBaseRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    criticalObservationRaw K m n i ∈ ArcBaseRing K m n hm hn := by
  rw [Valuation.mem_valuationSubring_iff]
  rw [criticalObservationArcValuation, Valuation.comap_apply]
  change Valued.v (criticalObservationArcEmbedding K hm hn
    (criticalObservationRaw K m n i)) ≤ 1
  rw [criticalObservationArcEmbedding_raw]
  apply (LaurentSeries.val_le_one_iff_eq_coe
    (CriticalArcConstants K m n) (criticalArcObservation K m n (Sum.inl i))).2
  exact ⟨powerSeriesCriticalObservation K (CriticalArcConstants K m n)
    (criticalArcRawDirection K m n) (criticalArcReciprocalDirection K m n) (Sum.inl i), rfl⟩

theorem criticalObservationRecip_mem_arcBaseRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    criticalObservationRecip K m n j ∈ ArcBaseRing K m n hm hn := by
  rw [Valuation.mem_valuationSubring_iff]
  rw [criticalObservationArcValuation, Valuation.comap_apply]
  change Valued.v (criticalObservationArcEmbedding K hm hn
    (criticalObservationRecip K m n j)) ≤ 1
  rw [criticalObservationArcEmbedding_recip]
  apply (LaurentSeries.val_le_one_iff_eq_coe
    (CriticalArcConstants K m n) (criticalArcObservation K m n (Sum.inr j))).2
  exact ⟨powerSeriesCriticalObservation K (CriticalArcConstants K m n)
    (criticalArcRawDirection K m n) (criticalArcReciprocalDirection K m n) (Sum.inr j), rfl⟩

noncomputable def criticalNormalClosureArcRawDeviationBase
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    ArcBaseRing K m n hm hn :=
  ⟨criticalObservationRaw K m n i -
      algebraMap K (criticalObservationField K m n)
        (criticalObservationShift K (Sum.inl i)), by
    rw [Valuation.mem_valuationSubring_iff,
      criticalObservationArcValuation_raw_sub_shift K hm hn]
    simpa only [WithZero.exp_zero] using
      (WithZero.exp_le_exp.mpr (show (-1 : ℤ) ≤ 0 by omega))⟩

noncomputable def criticalNormalClosureArcReciprocalDeviationBase
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    ArcBaseRing K m n hm hn :=
  ⟨criticalObservationRecip K m n j -
      algebraMap K (criticalObservationField K m n)
        (criticalObservationShift K (Sum.inr j)), by
    rw [Valuation.mem_valuationSubring_iff,
      criticalObservationArcValuation_recip_sub_shift K hm hn]
    simpa only [WithZero.exp_zero] using
      (WithZero.exp_le_exp.mpr (show (-1 : ℤ) ≤ 0 by omega))⟩

theorem criticalNormalClosureArcRawDeviationBase_mem_maximalIdeal
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    criticalNormalClosureArcRawDeviationBase K hm hn i ∈
      IsLocalRing.maximalIdeal (ArcBaseRing K m n hm hn) := by
  rw [Valuation.mem_maximalIdeal_iff]
  change criticalObservationArcValuation K hm hn
    (criticalObservationRaw K m n i -
      algebraMap K (criticalObservationField K m n)
        (criticalObservationShift K (Sum.inl i))) < 1
  rw [criticalObservationArcValuation_raw_sub_shift K hm hn]
  simpa only [WithZero.exp_zero] using
    (WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by omega))

theorem criticalNormalClosureArcReciprocalDeviationBase_mem_maximalIdeal
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    criticalNormalClosureArcReciprocalDeviationBase K hm hn j ∈
      IsLocalRing.maximalIdeal (ArcBaseRing K m n hm hn) := by
  rw [Valuation.mem_maximalIdeal_iff]
  change criticalObservationArcValuation K hm hn
    (criticalObservationRecip K m n j -
      algebraMap K (criticalObservationField K m n)
        (criticalObservationShift K (Sum.inr j))) < 1
  rw [criticalObservationArcValuation_recip_sub_shift K hm hn]
  simpa only [WithZero.exp_zero] using
    (WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by omega))

noncomputable def criticalNormalClosureArcRawDeviation
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    ArcValuationRing K m n hm hn :=
  algebraMap (ArcIntegralClosure K m n hm hn) (ArcValuationRing K m n hm hn)
    (algebraMap (ArcBaseRing K m n hm hn) (ArcIntegralClosure K m n hm hn)
      (criticalNormalClosureArcRawDeviationBase K hm hn i))

noncomputable def criticalNormalClosureArcReciprocalDeviation
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    ArcValuationRing K m n hm hn :=
  algebraMap (ArcIntegralClosure K m n hm hn) (ArcValuationRing K m n hm hn)
    (algebraMap (ArcBaseRing K m n hm hn) (ArcIntegralClosure K m n hm hn)
      (criticalNormalClosureArcReciprocalDeviationBase K hm hn j))

noncomputable def criticalNormalClosureArcRawCoefficient
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    ArcValuationRing K m n hm hn :=
  criticalNormalClosureArcRawDeviation K hm hn i + if (i : ℕ) = 0 then 1 else 0

noncomputable def criticalNormalClosureArcReciprocalCoefficient
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    ArcValuationRing K m n hm hn :=
  criticalNormalClosureArcReciprocalDeviation K hm hn j + if (j : ℕ) = 0 then 1 else 0

theorem criticalNormalClosureArcResidue_rawDeviation
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    IsLocalRing.residue (ArcValuationRing K m n hm hn)
      (criticalNormalClosureArcRawDeviation K hm hn i) = 0 := by
  let P := criticalNormalClosureArcPrime K m n hm hn
  letI : P.LiesOver (IsLocalRing.maximalIdeal (ArcBaseRing K m n hm hn)) :=
    criticalNormalClosureArcPrime_liesOver K m n hm hn
  rw [IsLocalRing.residue_eq_zero_iff]
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (ArcValuationRing K m n hm hn) P _).2
  exact (Ideal.mem_of_liesOver
    (P := P) (p := IsLocalRing.maximalIdeal (ArcBaseRing K m n hm hn)) _).1
      (criticalNormalClosureArcRawDeviationBase_mem_maximalIdeal K hm hn i)

theorem criticalNormalClosureArcResidue_reciprocalDeviation
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    IsLocalRing.residue (ArcValuationRing K m n hm hn)
      (criticalNormalClosureArcReciprocalDeviation K hm hn j) = 0 := by
  let P := criticalNormalClosureArcPrime K m n hm hn
  letI : P.LiesOver (IsLocalRing.maximalIdeal (ArcBaseRing K m n hm hn)) :=
    criticalNormalClosureArcPrime_liesOver K m n hm hn
  rw [IsLocalRing.residue_eq_zero_iff]
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (ArcValuationRing K m n hm hn) P _).2
  exact (Ideal.mem_of_liesOver
    (P := P) (p := IsLocalRing.maximalIdeal (ArcBaseRing K m n hm hn)) _).1
      (criticalNormalClosureArcReciprocalDeviationBase_mem_maximalIdeal K hm hn j)

@[simp] theorem criticalNormalClosureArcResidue_rawCoefficient
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    IsLocalRing.residue (ArcValuationRing K m n hm hn)
      (criticalNormalClosureArcRawCoefficient K hm hn i) =
      if (i : ℕ) = 0 then 1 else 0 := by
  simp [criticalNormalClosureArcRawCoefficient,
    criticalNormalClosureArcResidue_rawDeviation K hm hn i]

@[simp] theorem criticalNormalClosureArcResidue_reciprocalCoefficient
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    IsLocalRing.residue (ArcValuationRing K m n hm hn)
      (criticalNormalClosureArcReciprocalCoefficient K hm hn j) =
      if (j : ℕ) = 0 then 1 else 0 := by
  simp [criticalNormalClosureArcReciprocalCoefficient,
    criticalNormalClosureArcResidue_reciprocalDeviation K hm hn j]

theorem criticalNormalClosureArcRawDeviation_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    ((criticalNormalClosureArcRawDeviation K hm hn i : ArcValuationRing K m n hm hn) :
        criticalNormalClosure K m n) =
      criticalObservationNormalClosureMap K m n
        (criticalObservationRaw K m n i -
          algebraMap K (criticalObservationField K m n)
            (criticalObservationShift K (m := m) (n := n) (Sum.inl i))) := by
  exact criticalNormalClosureArcBase_toValuationRing_coe K m n hm hn
    (criticalNormalClosureArcRawDeviationBase K hm hn i)

theorem criticalNormalClosureArcReciprocalDeviation_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    ((criticalNormalClosureArcReciprocalDeviation K hm hn j :
        ArcValuationRing K m n hm hn) : criticalNormalClosure K m n) =
      criticalObservationNormalClosureMap K m n
        (criticalObservationRecip K m n j -
          algebraMap K (criticalObservationField K m n)
            (criticalObservationShift K (m := m) (n := n) (Sum.inr j))) := by
  exact criticalNormalClosureArcBase_toValuationRing_coe K m n hm hn
    (criticalNormalClosureArcReciprocalDeviationBase K hm hn j)

theorem criticalNormalClosureArcRawCoefficient_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    ((criticalNormalClosureArcRawCoefficient K hm hn i :
        ArcValuationRing K m n hm hn) : criticalNormalClosure K m n) =
      criticalObservationNormalClosureMap K m n
        (criticalObservationRaw K m n i) := by
  change (ArcValuationRing K m n hm hn).subtype
      (criticalNormalClosureArcRawDeviation K hm hn i +
        if (i : ℕ) = 0 then 1 else 0) = _
  rw [map_add]
  change ((criticalNormalClosureArcRawDeviation K hm hn i :
      ArcValuationRing K m n hm hn) : criticalNormalClosure K m n) + _ = _
  rw [criticalNormalClosureArcRawDeviation_coe K hm hn i]
  by_cases hi : (i : ℕ) = 0
  · simp [criticalObservationShift, hi]
  · simp [criticalObservationShift, hi]

theorem criticalNormalClosureArcReciprocalCoefficient_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    ((criticalNormalClosureArcReciprocalCoefficient K hm hn j :
        ArcValuationRing K m n hm hn) : criticalNormalClosure K m n) =
      criticalObservationNormalClosureMap K m n
        (criticalObservationRecip K m n j) := by
  change (ArcValuationRing K m n hm hn).subtype
      (criticalNormalClosureArcReciprocalDeviation K hm hn j +
        if (j : ℕ) = 0 then 1 else 0) = _
  rw [map_add]
  change ((criticalNormalClosureArcReciprocalDeviation K hm hn j :
      ArcValuationRing K m n hm hn) : criticalNormalClosure K m n) + _ = _
  rw [criticalNormalClosureArcReciprocalDeviation_coe K hm hn j]
  by_cases hj : (j : ℕ) = 0
  · simp [criticalObservationShift, hj]
  · simp [criticalObservationShift, hj]

/-- Explicit inclusion of the chosen arc DVR into the actual normal closure. -/
noncomputable def criticalNormalClosureArcSubtype
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ArcValuationRing K m n hm hn →+* criticalNormalClosure K m n :=
  (ArcValuationRing K m n hm hn).subtype

/-- Integral raw observed tail at the actual chosen place. -/
noncomputable def criticalNormalClosureArcRawTail
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (ArcValuationRing K m n hm hn)[X] :=
  ∑ i : Fin n,
    C (criticalNormalClosureArcRawCoefficient K hm hn i) * X ^ (m + (i : ℕ))

/-- Integral reciprocal observed tail at the actual chosen place. -/
noncomputable def criticalNormalClosureArcReciprocalTail
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (ArcValuationRing K m n hm hn)[X] :=
  ∑ j : Fin m,
    C (criticalNormalClosureArcReciprocalCoefficient K hm hn j) * X ^ (n + (j : ℕ))

set_option maxHeartbeats 5000000 in
theorem criticalNormalClosureArcRawTail_map_subtype
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureArcRawTail K hm hn).map
        (criticalNormalClosureArcSubtype K hm hn) =
      (criticalObservationRawTail K m n).map
        (criticalObservationNormalClosureMap K m n) := by
  classical
  rw [criticalNormalClosureArcRawTail, criticalObservationRawTail,
    Polynomial.map_sum, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  congr 2
  change ((criticalNormalClosureArcRawCoefficient K hm hn i :
    ArcValuationRing K m n hm hn) : criticalNormalClosure K m n) = _
  exact criticalNormalClosureArcRawCoefficient_coe K hm hn i

set_option maxHeartbeats 5000000 in
theorem criticalNormalClosureArcReciprocalTail_map_subtype
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureArcReciprocalTail K hm hn).map
        (criticalNormalClosureArcSubtype K hm hn) =
      (criticalObservationReciprocalTail K m n).map
        (criticalObservationNormalClosureMap K m n) := by
  classical
  rw [criticalNormalClosureArcReciprocalTail, criticalObservationReciprocalTail,
    Polynomial.map_sum, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  congr 2
  change ((criticalNormalClosureArcReciprocalCoefficient K hm hn j :
    ArcValuationRing K m n hm hn) : criticalNormalClosure K m n) = _
  exact criticalNormalClosureArcReciprocalCoefficient_coe K hm hn j

/-- A shifted finite tail whose constant coefficient reduces to one and whose later coefficients
reduce to zero has reduction `X ^ m`. -/
private theorem map_shiftedFiniteTail_eq_X_pow {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {m d : ℕ} (hd : 0 < d) (c : Fin d → R)
    (h0 : f (c ⟨0, hd⟩) = 1) (hlate : ∀ i : Fin d, (i : ℕ) ≠ 0 → f (c i) = 0) :
    (∑ i : Fin d, Polynomial.C (c i) * X ^ (m + (i : ℕ))).map f = (X : S[X]) ^ m := by
  classical
  rw [Polynomial.map_sum, Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp [h0]
  · intro i _ hi
    simp [hlate i fun h => hi (Fin.ext h)]
  · exact fun h => absurd (Finset.mem_univ (⟨0, hd⟩ : Fin d)) h

theorem criticalNormalClosureArcRawTail_map_residue
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureArcRawTail K hm hn).map
        (IsLocalRing.residue (ArcValuationRing K m n hm hn)) =
      (X : (IsLocalRing.ResidueField (ArcValuationRing K m n hm hn))[X]) ^ m := by
  refine map_shiftedFiniteTail_eq_X_pow _ hn _ (by simp) (fun i hi => by simp [hi])

theorem criticalNormalClosureArcReciprocalTail_map_residue
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureArcReciprocalTail K hm hn).map
        (IsLocalRing.residue (ArcValuationRing K m n hm hn)) =
      (X : (IsLocalRing.ResidueField (ArcValuationRing K m n hm hn))[X]) ^ n := by
  refine map_shiftedFiniteTail_eq_X_pow _ hm _ (by simp) (fun j hj => by simp [hj])

end

end GaloisForLFunctions.HTGeometry
