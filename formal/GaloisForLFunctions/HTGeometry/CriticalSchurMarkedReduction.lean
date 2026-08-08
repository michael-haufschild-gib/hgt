import GaloisForLFunctions.HTGeometry.CriticalSchurMarkedUnits
import GaloisForLFunctions.HTGeometry.CriticalSchurNormalFibreReduction

/-!
# Nonvanishing of the marked reduced tails at the Schur place

The marked two-sided source coordinates are units at the generic Schur divisor.  Their images in
the chosen normal-closure valuation ring remain units, so the marked coefficients of both reduced
observation tails are nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem criticalObservationRawTail_coeff_marked
    (K : Type*) [Field K] {m n : ℕ} (hn : 0 < n) :
    (criticalObservationRawTail K m n).coeff m =
      criticalObservationRaw K m n ⟨0, hn⟩ := by
  classical
  rw [criticalObservationRawTail, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single ⟨0, hn⟩]
  · simp
  · intro i hi hne
    rw [if_neg (by
      intro hindex
      apply hne
      apply Fin.ext
      change (i : ℕ) = 0
      omega), mul_zero]
  · intro hmissing
    exact (hmissing (Finset.mem_univ _)).elim

theorem criticalObservationReciprocalTail_coeff_marked
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) :
    (criticalObservationReciprocalTail K m n).coeff n =
      criticalObservationRecip K m n ⟨0, hm⟩ := by
  classical
  rw [criticalObservationReciprocalTail, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single ⟨0, hm⟩]
  · simp
  · intro j hj hne
    rw [if_neg (by
      intro hindex
      apply hne
      apply Fin.ext
      change (j : ℕ) = 0
      omega), mul_zero]
  · intro hmissing
    exact (hmissing (Finset.mem_univ _)).elim

/-- Integral source-valuation map into the chosen upper Schur valuation ring. -/
noncomputable def criticalSchurSourceValuationToUpper
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurSourceValuationSubring K hm hn →+*
      criticalNormalClosureSchurValuationSubring K hm hn :=
  (criticalSchurSourceValuationToNormalClosure K hm hn).codRestrict
    (criticalNormalClosureSchurValuationSubring K hm hn).toSubring
    (criticalNormalClosureSchurValuationSubring_source_mem K hm hn)

/-- The marked coefficient of the integral raw tail is an upper valuation unit. -/
theorem isUnit_criticalNormalClosureSchurRawTailIntegral_coeff_marked
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    IsUnit ((criticalNormalClosureSchurRawTailIntegral K (m := m) (n := n)
      (by omega) (by omega)).coeff m) := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  let x : criticalSchurSourceValuationSubring K hm0 hn0 :=
    ⟨criticalSourceRaw K m n ⟨m, by omega⟩,
      criticalSourceRaw_mem_sourceValuationSubring K hm0 hn0 ⟨m, by omega⟩⟩
  let f := criticalSchurSourceValuationToUpper K hm0 hn0
  have hxunit : IsUnit x :=
    isUnit_criticalSourceRaw_marked_sourceValuationSubring K hm hn
  have hmapunit : IsUnit (f x) := hxunit.map f
  have hcoeff := congrArg (fun P => P.coeff m)
    (map_criticalNormalClosureSchurRawTailIntegral K hm0 hn0)
  rw [Polynomial.coeff_map, Polynomial.coeff_map,
    criticalObservationRawTail_coeff_marked K hn0] at hcoeff
  have hobs : algebraMap (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalObservationRaw K m n ⟨0, hn0⟩) =
      criticalSourceRaw K m n ⟨m, by omega⟩ := by
    apply Subtype.ext
    rfl
  have heq : (criticalNormalClosureSchurRawTailIntegral K (m := m) (n := n)
      hm0 hn0).coeff m = f x := by
    apply Subtype.ext
    calc
      ((criticalNormalClosureSchurRawTailIntegral K (m := m) (n := n) hm0 hn0).coeff m :
          criticalNormalClosure K m n) =
          criticalObservationNormalClosureMap K m n
            (criticalObservationRaw K m n ⟨0, hn0⟩) := hcoeff
      _ = criticalSourceNormalClosureEmbedding K m n
          (algebraMap (criticalObservationField K m n)
            (criticalSourceField K m n) (criticalObservationRaw K m n ⟨0, hn0⟩)) :=
        ((criticalSourceNormalClosureEmbedding K m n).commutes _).symm
      _ = criticalSourceNormalClosureEmbedding K m n
          (criticalSourceRaw K m n ⟨m, by omega⟩) := by rw [hobs]
      _ = (f x : criticalNormalClosure K m n) := rfl
  rw [heq]
  exact hmapunit

/-- The marked coefficient of the integral reciprocal tail is an upper valuation unit. -/
theorem isUnit_criticalNormalClosureSchurReciprocalTailIntegral_coeff_marked
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    IsUnit ((criticalNormalClosureSchurReciprocalTailIntegral K (m := m) (n := n)
      (by omega) (by omega)).coeff n) := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  let x : criticalSchurSourceValuationSubring K hm0 hn0 :=
    ⟨criticalSourceRecip K m n ⟨n, by omega⟩,
      criticalSourceRecip_mem_sourceValuationSubring K hm0 hn0 ⟨n, by omega⟩⟩
  let f := criticalSchurSourceValuationToUpper K hm0 hn0
  have hxunit : IsUnit x :=
    isUnit_criticalSourceRecip_marked_sourceValuationSubring K hm hn
  have hmapunit : IsUnit (f x) := hxunit.map f
  have hcoeff := congrArg (fun P => P.coeff n)
    (map_criticalNormalClosureSchurReciprocalTailIntegral K hm0 hn0)
  rw [Polynomial.coeff_map, Polynomial.coeff_map,
    criticalObservationReciprocalTail_coeff_marked K hm0] at hcoeff
  have hobs : algebraMap (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalObservationRecip K m n ⟨0, hm0⟩) =
      criticalSourceRecip K m n ⟨n, by omega⟩ := by
    apply Subtype.ext
    rfl
  have heq : (criticalNormalClosureSchurReciprocalTailIntegral K (m := m) (n := n)
      hm0 hn0).coeff n = f x := by
    apply Subtype.ext
    calc
      ((criticalNormalClosureSchurReciprocalTailIntegral K (m := m) (n := n)
          hm0 hn0).coeff n :
          criticalNormalClosure K m n) =
          criticalObservationNormalClosureMap K m n
            (criticalObservationRecip K m n ⟨0, hm0⟩) := hcoeff
      _ = criticalSourceNormalClosureEmbedding K m n
          (algebraMap (criticalObservationField K m n)
            (criticalSourceField K m n) (criticalObservationRecip K m n ⟨0, hm0⟩)) :=
        ((criticalSourceNormalClosureEmbedding K m n).commutes _).symm
      _ = criticalSourceNormalClosureEmbedding K m n
          (criticalSourceRecip K m n ⟨n, by omega⟩) := by rw [hobs]
      _ = (f x : criticalNormalClosure K m n) := rfl
  rw [heq]
  exact hmapunit

/-- The marked raw coefficient remains nonzero after reduction at the upper Schur place. -/
theorem reduced_criticalNormalClosureSchurRawTailIntegral_coeff_marked_ne_zero
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    ((criticalNormalClosureSchurRawTailIntegral K (m := m) (n := n)
      (by omega) (by omega)).map
      (IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K (m := m) (n := n)
          (by omega) (by omega)))).coeff m ≠ 0 := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  rw [Polynomial.coeff_map]
  exact (isUnit_criticalNormalClosureSchurRawTailIntegral_coeff_marked K hm hn).map
    (IsLocalRing.residue
      (criticalNormalClosureSchurValuationSubring K (m := m) (n := n)
        hm0 hn0)) |>.ne_zero

/-- The marked reciprocal coefficient remains nonzero after reduction at the upper Schur place. -/
theorem reduced_criticalNormalClosureSchurReciprocalTailIntegral_coeff_marked_ne_zero
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    ((criticalNormalClosureSchurReciprocalTailIntegral K (m := m) (n := n)
      (by omega) (by omega)).map
      (IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K (m := m) (n := n)
          (by omega) (by omega)))).coeff n ≠ 0 := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  rw [Polynomial.coeff_map]
  exact (isUnit_criticalNormalClosureSchurReciprocalTailIntegral_coeff_marked K hm hn).map
    (IsLocalRing.residue
      (criticalNormalClosureSchurValuationSubring K (m := m) (n := n)
        hm0 hn0)) |>.ne_zero

end

end GaloisForLFunctions.HTGeometry
