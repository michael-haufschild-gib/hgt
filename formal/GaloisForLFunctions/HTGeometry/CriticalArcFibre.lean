import GaloisForLFunctions.HTGeometry.CriticalGenericArc
import GaloisForLFunctions.HTGeometry.GenericCriticalLaurentFibre

/-!
# Exact critical fibre on the actual observation-field arc

The common-scale embedding of the actual observation field lands on the Laurent deformation whose
critical fibre was counted exactly.  This module names that fibre and identifies each tail
coefficient with the image of the corresponding actual observation coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped LaurentSeries

noncomputable section

/-- Laurent field carrying the common-scale specialization of the actual observation field. -/
abbrev CriticalArcLaurentField
    (K : Type*) [Field K] (m n : ℕ) :=
  (CriticalArcConstants K m n)⸨X⸩

/-- Raw tail on the actual common-scale arc. -/
noncomputable def criticalArcRawTail
    (K : Type*) [Field K] (m n : ℕ) :
    (CriticalArcLaurentField K m n)[X] :=
  (X ^ m + powerSeriesRawDeformation (CriticalArcConstants K m n) m n
    (criticalArcRawDirection K m n)).map
      (algebraMap (PowerSeries (CriticalArcConstants K m n))
        (CriticalArcLaurentField K m n))

/-- Reciprocal tail on the actual common-scale arc. -/
noncomputable def criticalArcReciprocalTail
    (K : Type*) [Field K] (m n : ℕ) :
    (CriticalArcLaurentField K m n)[X] :=
  (X ^ n + powerSeriesReciprocalDeformation (CriticalArcConstants K m n) m n
    (criticalArcReciprocalDirection K m n)).map
      (algebraMap (PowerSeries (CriticalArcConstants K m n))
        (CriticalArcLaurentField K m n))

/-- Critical fibre on the actual observation-field common-scale arc. -/
abbrev CriticalArcFibre
    (K : Type*) [Field K] (m n : ℕ) :=
  criticalFibre (CriticalArcLaurentField K m n) m n
    (criticalArcRawTail K m n) (criticalArcReciprocalTail K m n)

/-- The raw arc tail begins in degree `m`. -/
theorem X_pow_dvd_criticalArcRawTail
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (CriticalArcLaurentField K m n)[X]) ^ m ∣ criticalArcRawTail K m n := by
  let f := algebraMap (PowerSeries (CriticalArcConstants K m n))
    (CriticalArcLaurentField K m n)
  have h : (X : (PowerSeries (CriticalArcConstants K m n))[X]) ^ m ∣
      X ^ m + powerSeriesRawDeformation (CriticalArcConstants K m n) m n
        (criticalArcRawDirection K m n) :=
    dvd_add (dvd_refl _) (polynomial_X_pow_dvd_powerSeriesRawDeformation
      (CriticalArcConstants K m n) m n (criticalArcRawDirection K m n))
  simpa [criticalArcRawTail, f] using Polynomial.map_dvd f h

/-- The reciprocal arc tail begins in degree `n`. -/
theorem X_pow_dvd_criticalArcReciprocalTail
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (CriticalArcLaurentField K m n)[X]) ^ n ∣
      criticalArcReciprocalTail K m n := by
  let f := algebraMap (PowerSeries (CriticalArcConstants K m n))
    (CriticalArcLaurentField K m n)
  have h : (X : (PowerSeries (CriticalArcConstants K m n))[X]) ^ n ∣
      X ^ n + powerSeriesReciprocalDeformation (CriticalArcConstants K m n) m n
        (criticalArcReciprocalDirection K m n) :=
    dvd_add (dvd_refl _) (polynomial_X_pow_dvd_powerSeriesReciprocalDeformation
      (CriticalArcConstants K m n) m n (criticalArcReciprocalDirection K m n))
  simpa [criticalArcReciprocalTail, f] using Polynomial.map_dvd f h

/-- Raw arc-tail coefficients are exactly the specialized actual raw observations. -/
theorem criticalArcRawTail_coeff
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    (criticalArcRawTail K m n).coeff (m + (i : ℕ)) =
      criticalObservationArcEmbedding K hm hn
        (criticalObservationRaw K m n i) := by
  rw [criticalArcRawTail, Polynomial.coeff_map, Polynomial.coeff_add,
    coeff_powerSeriesRawDeformation, criticalObservationArcEmbedding_raw]
  by_cases hi : (i : ℕ) = 0
  · simp [hi, criticalArcObservation, laurentCriticalObservation,
      powerSeriesCriticalObservation, criticalObservationShift,
      criticalDirectionConstants, add_comm]
  · simp [hi, criticalArcObservation, laurentCriticalObservation,
      powerSeriesCriticalObservation, criticalObservationShift,
      criticalDirectionConstants]

/-- Reciprocal arc-tail coefficients are exactly the specialized reciprocal observations. -/
theorem criticalArcReciprocalTail_coeff
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    (criticalArcReciprocalTail K m n).coeff (n + (j : ℕ)) =
      criticalObservationArcEmbedding K hm hn
        (criticalObservationRecip K m n j) := by
  rw [criticalArcReciprocalTail, Polynomial.coeff_map, Polynomial.coeff_add,
    coeff_powerSeriesReciprocalDeformation, criticalObservationArcEmbedding_recip]
  by_cases hj : (j : ℕ) = 0
  · simp [hj, criticalArcObservation, laurentCriticalObservation,
      powerSeriesCriticalObservation, criticalObservationShift,
      criticalDirectionConstants, add_comm]
  · simp [hj, criticalArcObservation, laurentCriticalObservation,
      powerSeriesCriticalObservation, criticalObservationShift,
      criticalDirectionConstants]

/-- The raw arc tail has no coefficient at or beyond the critical horizon. -/
theorem criticalArcRawTail_coeff_eq_zero_of_add_le
    (K : Type*) [Field K] {m n k : ℕ} (hn : 0 < n) (hk : m + n ≤ k) :
    (criticalArcRawTail K m n).coeff k = 0 := by
  classical
  rw [criticalArcRawTail, Polynomial.coeff_map, Polynomial.coeff_add]
  have hX : ((X : (PowerSeries (CriticalArcConstants K m n))[X]) ^ m).coeff k = 0 := by
    rw [Polynomial.coeff_X_pow, if_neg]
    omega
  rw [hX, zero_add, powerSeriesRawDeformation, Polynomial.finsetSum_coeff]
  have hsum :
      ∑ i : Fin n,
        (C (powerSeriesDeformParam (criticalArcRawDirection K m n i)) *
          X ^ (m + (i : ℕ)) : (PowerSeries (CriticalArcConstants K m n))[X]).coeff k = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    omega
  rw [hsum, map_zero]

/-- The reciprocal arc tail has no coefficient at or beyond the critical horizon. -/
theorem criticalArcReciprocalTail_coeff_eq_zero_of_add_le
    (K : Type*) [Field K] {m n k : ℕ} (hm : 0 < m) (hk : m + n ≤ k) :
    (criticalArcReciprocalTail K m n).coeff k = 0 := by
  classical
  rw [criticalArcReciprocalTail, Polynomial.coeff_map, Polynomial.coeff_add]
  have hX : ((X : (PowerSeries (CriticalArcConstants K m n))[X]) ^ n).coeff k = 0 := by
    rw [Polynomial.coeff_X_pow, if_neg]
    omega
  rw [hX, zero_add, powerSeriesReciprocalDeformation, Polynomial.finsetSum_coeff]
  have hsum :
      ∑ j : Fin m,
        (C (powerSeriesDeformParam (criticalArcReciprocalDirection K m n j)) *
          X ^ (n + (j : ℕ)) : (PowerSeries (CriticalArcConstants K m n))[X]).coeff k = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    omega
  rw [hsum, map_zero]

/-- The actual common-scale arc fibre has the exact critical multiplicity. -/
theorem natCard_criticalArcFibre
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (CriticalArcFibre K m n) = criticalHorizonMultiplicity m n := by
  exact nat_card_laurentSeriesCriticalFibre (CriticalArcConstants K m n) hm hn
    (criticalArcRawDirection K m n) (criticalArcReciprocalDirection K m n)

end

end GaloisForLFunctions.HTGeometry
