import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointDipoleInverseSquareEnergy
import GaloisForLFunctions.HTGeometry.PhaseGridApproximation

/-!
# Active-aperture width control of physical endpoint energy

For an active clipped prime interval, the endpoint chord is at most its angular arc and clipping
cannot increase the raw aperture width.  These source identities eliminate the dipole variable
from the physical inverse-square energy law, leaving only aperture width and total prime weight.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The chord of one active physical prime interval is at most its angular arc. -/
theorem norm_xiPhysicalPrimeLogEndpointChord_le_two_pi_div_mul_length
    {A m k : ℝ} (hA : 0 < A) (p : Nat.Primes)
    (hactive : 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureEnd A k p)) -
      fourier 1 (xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureStart m p))‖ ≤
      (2 * Real.pi / A) * xiPhysicalPrimeLogApertureLength A m k p := by
  let e := xiPhysicalPrimeLogApertureEnd A k p
  let s := xiPhysicalPrimeLogApertureStart m p
  let L := xiPhysicalPrimeLogApertureLength A m k p
  have hdiff : 0 < e - s := by
    simpa [L, xiPhysicalPrimeLogApertureLength, e, s] using hactive
  have hL : L = e - s := by
    dsimp only [L, e, s]
    rw [xiPhysicalPrimeLogApertureLength, max_eq_right]
    exact hdiff.le
  change ‖fourier 1 (e : AddCircle A) - fourier 1 (s : AddCircle A)‖ ≤
    (2 * Real.pi / A) * L
  rw [fourier_coe_apply, fourier_coe_apply]
  have h := GaloisForLFunctions.HTGeometry.norm_exp_sub_exp_le
    (2 * Real.pi * e / A) (2 * Real.pi * s / A)
  have hexpE :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (e : ℂ) / (A : ℂ)) =
        Complex.exp (((2 * Real.pi * e / A : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  have hexpS :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (s : ℂ) / (A : ℂ)) =
        Complex.exp (((2 * Real.pi * s / A : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexpE, hexpS]
  calc
    _ ≤ |2 * Real.pi * e / A - 2 * Real.pi * s / A| := h
    _ = (2 * Real.pi / A) * L := by
      rw [hL]
      have hcoef : 0 < 2 * Real.pi / A := div_pos (mul_pos two_pos Real.pi_pos) hA
      rw [show 2 * Real.pi * e / A - 2 * Real.pi * s / A =
          (2 * Real.pi / A) * (e - s) by ring,
        abs_of_pos (mul_pos hcoef hdiff)]

/-- Clipping at `0` and `A` cannot make an active prime interval longer than raw width `k-m`. -/
theorem xiPhysicalPrimeLogApertureLength_le_width_of_active
    {A m k : ℝ} (p : Nat.Primes)
    (hactive : 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogApertureLength A m k p ≤ k - m := by
  let e := xiPhysicalPrimeLogApertureEnd A k p
  let s := xiPhysicalPrimeLogApertureStart m p
  have hdiff : 0 < e - s := by
    simpa [xiPhysicalPrimeLogApertureLength, e, s] using hactive
  have hlen : xiPhysicalPrimeLogApertureLength A m k p = e - s := by
    rw [xiPhysicalPrimeLogApertureLength, max_eq_right]
    exact hdiff.le
  have he : e ≤ k - Real.log (p : ℝ) := min_le_right _ _
  have hs : m - Real.log (p : ℝ) ≤ s := le_max_right _ _
  rw [hlen]
  linarith

/-- Weighted physical dipole chord is bounded by weighted clipped-interval length. -/
theorem xiPhysicalPrimeLogEndpointDipoleChordMass_le_two_pi_div_mul_weightedLengthMass
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogEndpointDipoleChordMass P A m k ≤
      (2 * Real.pi / A) *
        xiPhysicalPrimeLogApertureWeightedLengthMass P A m k := by
  rw [xiPhysicalPrimeLogEndpointDipoleChordMass,
    xiPhysicalPrimeLogApertureWeightedLengthMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hw := (physicalPrimeEndpointWeight_pos p).le
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left
      (norm_xiPhysicalPrimeLogEndpointChord_le_two_pi_div_mul_length
        hA p (hactive p hp)) hw

/-- Weighted clipped length is at most aperture width times total prime weight. -/
theorem xiPhysicalPrimeLogApertureWeightedLengthMass_le_width_mul_totalWeight
    (P : Finset Nat.Primes) {A m k : ℝ}
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogApertureWeightedLengthMass P A m k ≤
      (k - m) * xiPhysicalPrimeLogEndpointTotalWeight P := by
  rw [xiPhysicalPrimeLogApertureWeightedLengthMass,
    xiPhysicalPrimeLogEndpointTotalWeight, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left
      (xiPhysicalPrimeLogApertureLength_le_width_of_active p (hactive p hp))
      (physicalPrimeEndpointWeight_pos p).le

/-- Complete raw FCRJ ultraviolet energy is controlled explicitly by aperture width and total
prime weight; no endpoint-separation or dipole variable remains. -/
theorem natCast_mul_tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude_le_apertureWidth
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * ∑' r : ℕ,
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k) ≤
      (2 * A / Real.pi) * (N : ℝ) * (k - m) *
        xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := by
  by_cases hPempty : P = ∅
  · subst P
    simp [xiPhysicalPrimeLogEndpointTotalWeight,
      xiPhysicalPrimeLogCharacterAmplitude]
  let W := xiPhysicalPrimeLogEndpointTotalWeight P
  have hW : 0 ≤ W := xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  have hwidth : 0 ≤ k - m := by
    have hp : ∀ p ∈ P, 0 < k - m := fun p hp =>
      lt_of_lt_of_le (hactive p hp)
        (xiPhysicalPrimeLogApertureLength_le_width_of_active p (hactive p hp))
    have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPempty
    exact (hp hP.choose hP.choose_spec).le
  have hD :=
    xiPhysicalPrimeLogEndpointDipoleChordMass_le_two_pi_div_mul_weightedLengthMass
      P hA hactive
  have hL := xiPhysicalPrimeLogApertureWeightedLengthMass_le_width_mul_totalWeight
    P hactive
  have hsource :=
    natCast_mul_tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude_le_weight_chord
      P hA hactive N hN
  have hpi : 0 < Real.pi := Real.pi_pos
  calc
    _ ≤ (A ^ 2 / (4 * Real.pi ^ 2)) *
        (4 * (N : ℝ) * xiPhysicalPrimeLogEndpointTotalWeight P *
          xiPhysicalPrimeLogEndpointDipoleChordMass P A m k) := hsource
    _ ≤ (A ^ 2 / (4 * Real.pi ^ 2)) *
        (4 * (N : ℝ) * xiPhysicalPrimeLogEndpointTotalWeight P *
          ((2 * Real.pi / A) *
            xiPhysicalPrimeLogApertureWeightedLengthMass P A m k)) := by
      gcongr
    _ ≤ (A ^ 2 / (4 * Real.pi ^ 2)) *
        (4 * (N : ℝ) * xiPhysicalPrimeLogEndpointTotalWeight P *
          ((2 * Real.pi / A) *
            ((k - m) * xiPhysicalPrimeLogEndpointTotalWeight P))) := by
      gcongr
    _ = (2 * A / Real.pi) * (N : ℝ) * (k - m) *
        xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 := by
      field_simp [hA.ne', hpi.ne']

end

end RHTower
