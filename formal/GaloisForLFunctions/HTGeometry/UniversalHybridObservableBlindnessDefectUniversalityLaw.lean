import GaloisForLFunctions.HTGeometry.UniversalOrientedObservableGaugeBlindness
import GaloisForLFunctions.HTGeometry.UniversalPrimeObservableDephasingGeometry

/-!
# Universal hybrid observable-blindness defect

Finite differential observable fields are simultaneously blind to the integer orientation chamber
and the finite prime-residue chamber.  A single nonnegative hybrid defect, obtained by adding the
orientation index to the prime dephasing energy, vanishes exactly when both analytic Herglotz
channels are positive.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

/-- Joint defect of an integer orientation chamber and a finite prime-residue chamber. -/
def universalHybridOrientationDephasingDefect
    (k : ℕ) (J : Finset Nat.Primes) : ℝ :=
  (k : ℝ) + primeChamberDephasingMasterEnergy J ∅

/-- The hybrid defect is orientation index plus exact prime-chamber Hamming distance. -/
theorem universalHybridOrientationDephasingDefect_eq_index_add_hamming
    (k : ℕ) (J : Finset Nat.Primes) :
    universalHybridOrientationDephasingDefect k J =
      (k : ℝ) + (primeChamberHammingDistance J ∅ : ℝ) := by
  rw [universalHybridOrientationDephasingDefect,
    primeChamberDephasingMasterEnergy_eq_hamming]

/-- The joint defect vanishes only in the all-positive chamber on both axes. -/
theorem universalHybridOrientationDephasingDefect_eq_zero_iff
    (k : ℕ) (J : Finset Nat.Primes) :
    universalHybridOrientationDephasingDefect k J = 0 ↔ k = 0 ∧ J = ∅ := by
  rw [universalHybridOrientationDephasingDefect_eq_index_add_hamming]
  constructor
  · intro hzero
    have hk0 : (k : ℝ) = 0 := by
      nlinarith [(Nat.cast_nonneg k : 0 ≤ (k : ℝ)),
        (Nat.cast_nonneg (primeChamberHammingDistance J ∅) :
          0 ≤ (primeChamberHammingDistance J ∅ : ℝ))]
    have hd0 : (primeChamberHammingDistance J ∅ : ℝ) = 0 := by
      nlinarith [(Nat.cast_nonneg k : 0 ≤ (k : ℝ)),
        (Nat.cast_nonneg (primeChamberHammingDistance J ∅) :
          0 ≤ (primeChamberHammingDistance J ∅ : ℝ))]
    have henergy : primeChamberDephasingMasterEnergy J ∅ = 0 := by
      rw [primeChamberDephasingMasterEnergy_eq_hamming]
      exact hd0
    exact ⟨Nat.cast_eq_zero.mp hk0,
      (primeChamberDephasingMasterEnergy_eq_zero_iff J ∅).mp henergy⟩
  · rintro ⟨rfl, rfl⟩
    simp [primeChamberHammingDistance]

/-- **Hybrid observable-blindness/discriminator law.**  Oriented and prime-residue chambers have
the same differential observable field at every finite resolution.  Both Herglotz conditions hold
exactly when their single hybrid defect vanishes, and that defect is the sum of the integer
orientation index and prime Hamming distance. -/
theorem universalHybridChamber_sameObservableField_Herglotz_iff_defect_zero
    (k : ℕ) (J : Finset Nat.Primes) (N : UniversalFacetOrbitIndex → ℕ) :
    let S := universalOrientationSupport k
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitOrientedSource S S) N =
        differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitPrimeOrientedSource J) N ∧
      (((∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S S z).im) ∧
          (∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientedHerglotz J z).im)) ↔
        universalHybridOrientationDephasingDefect k J = 0) ∧
      universalHybridOrientationDephasingDefect k J =
        (k : ℝ) + (primeChamberHammingDistance J ∅ : ℝ) := by
  dsimp only
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  have hOrient := universalOrientationIndex_sameObservableField_while_Herglotz_iff_zero k N
  have hPrime := universalPrimeChamber_sameObservableField_while_Herglotz_iff_energy_zero J N
  refine ⟨(universalFacetOrbitOrientedSource_familyObservableField_eq
      (universalOrientationSupport k) (universalOrientationSupport k) N).trans
      (universalFacetOrbitPrimeOrientedSource_familyObservableField_eq J N).symm,
    ?_, universalHybridOrientationDephasingDefect_eq_index_add_hamming k J⟩
  constructor
  · rintro ⟨hO, hP⟩
    apply (universalHybridOrientationDephasingDefect_eq_zero_iff k J).mpr
    exact ⟨hOrient.2.1.mp hO,
      (primeChamberDephasingMasterEnergy_eq_zero_iff J ∅).mp (hPrime.2.mp hP)⟩
  · intro hzero
    obtain ⟨hk, hJ⟩ :=
      (universalHybridOrientationDephasingDefect_eq_zero_iff k J).mp hzero
    refine ⟨hOrient.2.1.mpr hk, hPrime.2.mpr ?_⟩
    exact (primeChamberDephasingMasterEnergy_eq_zero_iff J ∅).mpr hJ

end

end GaloisForLFunctions.HTGeometry
