import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureHilbertMetric
import GaloisForLFunctions.HTGeometry.FiniteHilbertDispersion

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Total physical ordinary-prime endpoint weight of a finite active packet. -/
def xiPhysicalPrimeLogTotalWeight (P : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ P, physicalPrimeEndpointWeight p

theorem xiPhysicalPrimeLogTotalWeight_pos
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    0 < xiPhysicalPrimeLogTotalWeight P := by
  rw [xiPhysicalPrimeLogTotalWeight]
  exact Finset.sum_pos (fun p hp => physicalPrimeEndpointWeight_pos p) hP

/-- `(AH13)`: normalized radius moment minus half ordered pairwise aperture dispersion. -/
def xiPhysicalPrimeLogNormalizedApertureDispersion
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  (∑ p ∈ P,
      (physicalPrimeEndpointWeight p / xiPhysicalPrimeLogTotalWeight P) *
        ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ ^ 2) -
    (1 / 2 : ℝ) *
      ∑ p ∈ P, ∑ q ∈ P,
        (physicalPrimeEndpointWeight p / xiPhysicalPrimeLogTotalWeight P) *
          (physicalPrimeEndpointWeight q / xiPhysicalPrimeLogTotalWeight P) *
            xiPhysicalPrimeLogApertureHilbertDistance A m k p q ^ 2

/-- `(AH14)`, Hilbert half: normalized aperture dispersion is exactly coherent fusion energy
divided by the square of total physical weight. -/
theorem xiPhysicalPrimeLogNormalizedApertureDispersion_eq_fusionEnergy_div
    {P : Finset Nat.Primes} (hP : P.Nonempty) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    xiPhysicalPrimeLogNormalizedApertureDispersion P A m k =
      xiPhysicalPrimeLogApertureFusionEnergy P A m k /
        xiPhysicalPrimeLogTotalWeight P ^ 2 := by
  have hW : ∑ p ∈ P, physicalPrimeEndpointWeight p ≠ 0 := by
    simpa [xiPhysicalPrimeLogTotalWeight] using
      (xiPhysicalPrimeLogTotalWeight_pos hP).ne'
  have hdisp := GaloisForLFunctions.HTGeometry.finite_normalized_weighted_hilbert_dispersion
    P (fun p : Nat.Primes => physicalPrimeEndpointWeight p)
      (xiPhysicalPrimeLogCenteredApertureCarrier A m k) hW
  change ‖xiPhysicalPrimeLogAggregateApertureCarrier P A m k‖ ^ 2 /
      (∑ p ∈ P, physicalPrimeEndpointWeight p) ^ 2 = _ at hdisp
  rw [← xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA m k] at hdisp
  rw [xiPhysicalPrimeLogNormalizedApertureDispersion, xiPhysicalPrimeLogTotalWeight]
  simpa only [xiPhysicalPrimeLogApertureHilbertDistance, dist_eq_norm] using hdisp.symm

/-- Exact unnormalized form `‖P_M‖² = W_M² Disp_M`. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_eq_totalWeight_sq_mul_dispersion
    {P : Finset Nat.Primes} (hP : P.Nonempty) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k =
      xiPhysicalPrimeLogTotalWeight P ^ 2 *
        xiPhysicalPrimeLogNormalizedApertureDispersion P A m k := by
  rw [xiPhysicalPrimeLogNormalizedApertureDispersion_eq_fusionEnergy_div hP hA]
  field_simp [(xiPhysicalPrimeLogTotalWeight_pos hP).ne']

theorem xiPhysicalPrimeLogNormalizedApertureDispersion_nonneg
    {P : Finset Nat.Primes} (hP : P.Nonempty) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    0 ≤ xiPhysicalPrimeLogNormalizedApertureDispersion P A m k := by
  rw [xiPhysicalPrimeLogNormalizedApertureDispersion_eq_fusionEnergy_div hP hA]
  exact div_nonneg (xiPhysicalPrimeLogApertureFusionEnergy_nonneg P hA m k)
    (sq_nonneg _)

/-- Strict dispersion is equivalent to nonvanishing of the exact coherent physical carrier. -/
theorem xiPhysicalPrimeLogNormalizedApertureDispersion_pos_iff
    {P : Finset Nat.Primes} (hP : P.Nonempty) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    0 < xiPhysicalPrimeLogNormalizedApertureDispersion P A m k ↔
      xiPhysicalPrimeLogAggregateApertureCarrier P A m k ≠ 0 := by
  rw [xiPhysicalPrimeLogNormalizedApertureDispersion_eq_fusionEnergy_div hP hA,
    xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA m k]
  have hWsq : 0 < xiPhysicalPrimeLogTotalWeight P ^ 2 :=
    sq_pos_of_pos (xiPhysicalPrimeLogTotalWeight_pos hP)
  constructor
  · intro h
    rcases div_pos_iff.mp h with hpos | hneg
    · intro hz
      simp [hz] at hpos
    · exact False.elim ((not_lt_of_ge hWsq.le) hneg.2)
  · intro hne
    exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hne)) hWsq

/-- `(AH15)`: a fusion-energy budget is exactly the normalized-dispersion budget. -/
theorem xiPhysicalPrimeLogFusionEnergy_le_iff_dispersion_le
    {P : Finset Nat.Primes} (hP : P.Nonempty) {A : ℝ} (hA : 0 < A)
    (m k budget : ℝ) :
    xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤ budget ↔
      xiPhysicalPrimeLogNormalizedApertureDispersion P A m k ≤
        budget / xiPhysicalPrimeLogTotalWeight P ^ 2 := by
  rw [xiPhysicalPrimeLogNormalizedApertureDispersion_eq_fusionEnergy_div hP hA]
  exact (div_le_div_iff_of_pos_right
    (sq_pos_of_pos (xiPhysicalPrimeLogTotalWeight_pos hP))).symm

end
end RHTower
