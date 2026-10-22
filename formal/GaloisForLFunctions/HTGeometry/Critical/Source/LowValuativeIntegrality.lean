import GaloisForLFunctions.HTGeometry.CriticalLowBlockValuativeIntegrality
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Geometric.SheetFibre

/-!
# The critical low coordinates are integral over the observation chart

Splitting the raw and reciprocal truncations into low block and observed tail turns the horizon
relation into a critical relation whose tails are the observation coordinates.  Valuative
integrality of the low blocks therefore says: every valuation subring of the source field that
contains the observation coordinates and inverts the two marked ones already contains all the low
raw and reciprocal coordinates.

Through the valuative criterion for integral closure this is the statement that the critical map
is finite over the marked chart.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 1000000

variable (K : Type*) [Field K] {m n : ℕ}

theorem algebraMap_criticalObservationRaw (i : Fin n) :
    algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalObservationRaw K m n i) = criticalSourceRaw K m n ⟨m + (i : ℕ), by omega⟩ :=
  Subtype.ext rfl

theorem algebraMap_criticalObservationRecip (j : Fin m) :
    algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
      (criticalObservationRecip K m n j) = criticalSourceRecip K m n ⟨n + (j : ℕ), by omega⟩ :=
  Subtype.ext rfl

theorem coeff_map_criticalObservationRawTail_mem
    (O : ValuationSubring (criticalSourceField K m n))
    (hraw : ∀ i : Fin n, criticalSourceRaw K m n ⟨m + (i : ℕ), by omega⟩ ∈ O) (k : ℕ) :
    ((criticalObservationRawTail K m n).map
      (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))).coeff k ∈ O := by
  classical
  rw [criticalObservationRawTail, Polynomial.map_sum, Polynomial.finsetSum_coeff]
  refine sum_mem fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : k = m + (i : ℕ)
  · rw [if_pos h, mul_one, algebraMap_criticalObservationRaw]
    exact hraw i
  · rw [if_neg h, mul_zero]
    exact O.zero_mem

theorem coeff_map_criticalObservationRecipTail_mem
    (O : ValuationSubring (criticalSourceField K m n))
    (hrecip : ∀ j : Fin m, criticalSourceRecip K m n ⟨n + (j : ℕ), by omega⟩ ∈ O) (k : ℕ) :
    ((criticalObservationReciprocalTail K m n).map
      (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))).coeff k ∈ O := by
  classical
  rw [criticalObservationReciprocalTail, Polynomial.map_sum, Polynomial.finsetSum_coeff]
  refine sum_mem fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : k = n + (j : ℕ)
  · rw [if_pos h, mul_one, algebraMap_criticalObservationRecip]
    exact hrecip j
  · rw [if_neg h, mul_zero]
    exact O.zero_mem

theorem coeff_map_criticalObservationRawTail_marked (hn : 0 < n) :
    ((criticalObservationRawTail K m n).map
      (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))).coeff m
      = criticalSourceRaw K m n ⟨m, by omega⟩ := by
  classical
  rw [criticalObservationRawTail, Polynomial.map_sum, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by simp), mul_one,
      algebraMap_criticalObservationRaw]
    congr 1
  · intro i _ hi
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro h
    exact hi (Fin.ext (show (i : ℕ) = 0 by omega))
  · exact fun h => absurd (Finset.mem_univ _) h

theorem coeff_map_criticalObservationRecipTail_marked (hm : 0 < m) :
    ((criticalObservationReciprocalTail K m n).map
      (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))).coeff n
      = criticalSourceRecip K m n ⟨n, by omega⟩ := by
  classical
  rw [criticalObservationReciprocalTail, Polynomial.map_sum, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos (by simp), mul_one,
      algebraMap_criticalObservationRecip]
    congr 1
  · intro j _ hj
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro h
    exact hj (Fin.ext (show (j : ℕ) = 0 by omega))
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **The critical low coordinates lie in every valuation subring containing the observation
coordinates with the marked ones inverted.** -/
theorem criticalSourceLow_mem_valuationSubring (hm : 0 < m) (hn : 0 < n)
    (O : ValuationSubring (criticalSourceField K m n))
    (hraw : ∀ i : Fin n, criticalSourceRaw K m n ⟨m + (i : ℕ), by omega⟩ ∈ O)
    (hrecip : ∀ j : Fin m, criticalSourceRecip K m n ⟨n + (j : ℕ), by omega⟩ ∈ O)
    (hmraw : (criticalSourceRaw K m n ⟨m, by omega⟩)⁻¹ ∈ O)
    (hmrecip : (criticalSourceRecip K m n ⟨n, by omega⟩)⁻¹ ∈ O)
    (hmraw0 : criticalSourceRaw K m n ⟨m, by omega⟩ ≠ 0)
    (hmrecip0 : criticalSourceRecip K m n ⟨n, by omega⟩ ≠ 0) :
    (∀ i : Fin m, criticalSourceRaw K m n ⟨(i : ℕ), by omega⟩ ∈ O) ∧
      (∀ j : Fin n, criticalSourceRecip K m n ⟨(j : ℕ), by omega⟩ ∈ O) := by
  classical
  set φ := algebraMap (criticalObservationField K m n) (criticalSourceField K m n) with hφ
  set Utail := (criticalObservationRawTail K m n).map φ with hUt
  set Wtail := (criticalObservationReciprocalTail K m n).map φ with hWt
  have hAdeg : (criticalSourceRawLow K m n).natDegree < m := by
    by_cases h0 : criticalSourceRawLow K m n = 0
    · rw [h0]; simpa using hm
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (lowPolynomial_degree_lt _)
  have hBdeg : (criticalSourceReciprocalLow K m n).natDegree < n := by
    by_cases h0 : criticalSourceReciprocalLow K m n = 0
    · rw [h0]; simpa using hn
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (lowPolynomial_degree_lt _)
  have hUm : Utail.coeff m = criticalSourceRaw K m n ⟨m, by omega⟩ :=
    coeff_map_criticalObservationRawTail_marked K hn
  have hWn : Wtail.coeff n = criticalSourceRecip K m n ⟨n, by omega⟩ :=
    coeff_map_criticalObservationRecipTail_marked K hm
  have hdvd : (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣
      (criticalSourceRawLow K m n + Utail) *
        (criticalSourceReciprocalLow K m n + Wtail) - 1 := by
    rw [hUt, hWt, ← criticalSourceRawPolynomial_eq_low_add_tail,
      ← criticalSourceReciprocalPolynomial_eq_low_add_tail]
    exact X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n
  obtain ⟨hA, hB⟩ := coeffs_mem_of_criticalRelation O hAdeg hBdeg
    (coeff_map_criticalObservationRawTail_mem K O hraw)
    (coeff_map_criticalObservationRecipTail_mem K O hrecip)
    (by rw [hUm]; exact hmraw0) (by rw [hWn]; exact hmrecip0)
    (by rw [hUm]; exact hmraw) (by rw [hWn]; exact hmrecip) hdvd
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have h := hA (i : ℕ)
    rwa [criticalSourceRawLow, lowPolynomial_coeff, dif_pos i.isLt] at h
  · have h := hB (j : ℕ)
    rwa [criticalSourceReciprocalLow, lowPolynomial_coeff, dif_pos j.isLt] at h

end GaloisForLFunctions.HTGeometry
