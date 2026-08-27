import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointPhaseCollisionTailRate
import GaloisForLFunctions.HTGeometry.CirclePowerEstimates

/-!
# Primewise dipole multipole bounds for physical endpoints

The signed physical endpoint measure is exactly neutral: every prime contributes one positive end
and one negative start of the same weight.  Its `n`th circle moment is consequently controlled by
the weighted primewise endpoint chord times `n`, while total variation supplies the complementary
uniform bound.  This replaces unresolved endpoint-pair mass by a source-derived dipole moment.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Total unsigned ordinary-prime endpoint weight. -/
def xiPhysicalPrimeLogEndpointTotalWeight (P : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ P, physicalPrimeEndpointWeight p

/-- Weighted first chord moment of the literal primewise endpoint dipoles. -/
def xiPhysicalPrimeLogEndpointDipoleChordMass
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  ∑ p ∈ P, physicalPrimeEndpointWeight p *
    ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureEnd A k p)) -
      fourier 1 (xiPhysicalPrimeLogEndpointNode A
        (xiPhysicalPrimeLogApertureStart m p))‖

/-- Exact neutrality of the signed physical endpoint measure. -/
theorem sum_xiPhysicalPrimeLogEndpointCircleJump_eq_zero
    (P : Finset Nat.Primes) (A m k : ℝ) :
    ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
      xiPhysicalPrimeLogEndpointCircleJump P A m k x = 0 := by
  have h := sum_endpointCircleJump_mul P A m k (fun _ => (1 : ℂ))
  simpa using h

/-- First-multipole bound: an unresolved physical endpoint moment costs its weighted primewise
chord mass rather than full endpoint variation. -/
theorem norm_xiPhysicalPrimeLogEndpointCircleMoment_le_nat_mul_dipoleChordMass
    (P : Finset Nat.Primes) (A m k : ℝ) (n : ℕ) :
    ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ≤
      (n : ℝ) * xiPhysicalPrimeLogEndpointDipoleChordMass P A m k := by
  rw [xiPhysicalPrimeLogEndpointCircleMoment,
    sum_endpointCircleJump_mul P A m k
      (fun x : AddCircle A => fourier 1 x ^ n)]
  calc
    ‖∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) *
        (fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureEnd A k p)) ^ n -
          fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureStart m p)) ^ n)‖ ≤
      ∑ p ∈ P, ‖(physicalPrimeEndpointWeight p : ℂ) *
        (fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureEnd A k p)) ^ n -
          fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureStart m p)) ^ n)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, physicalPrimeEndpointWeight p *
        ((n : ℝ) * ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureEnd A k p)) -
          fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureStart m p))‖) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, norm_real,
        Real.norm_of_nonneg (physicalPrimeEndpointWeight_pos p).le]
      exact mul_le_mul_of_nonneg_left
        (GaloisForLFunctions.norm_pow_sub_pow_le_of_norm_one
          (by simp) (by simp) n)
        (physicalPrimeEndpointWeight_pos p).le
    _ = _ := by
      rw [xiPhysicalPrimeLogEndpointDipoleChordMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Uniform total-variation bound for every physical endpoint moment. -/
theorem norm_xiPhysicalPrimeLogEndpointCircleMoment_le_two_mul_totalWeight
    (P : Finset Nat.Primes) (A m k : ℝ) (n : ℕ) :
    ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ≤
      2 * xiPhysicalPrimeLogEndpointTotalWeight P := by
  rw [xiPhysicalPrimeLogEndpointCircleMoment,
    sum_endpointCircleJump_mul P A m k
      (fun x : AddCircle A => fourier 1 x ^ n)]
  calc
    ‖∑ p ∈ P, (physicalPrimeEndpointWeight p : ℂ) *
        (fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureEnd A k p)) ^ n -
          fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureStart m p)) ^ n)‖ ≤
      ∑ p ∈ P, ‖(physicalPrimeEndpointWeight p : ℂ) *
        (fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureEnd A k p)) ^ n -
          fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureStart m p)) ^ n)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, 2 * physicalPrimeEndpointWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, norm_real,
        Real.norm_of_nonneg (physicalPrimeEndpointWeight_pos p).le]
      have hdiff : ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureEnd A k p)) ^ n -
          fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureStart m p)) ^ n‖ ≤ 2 := by
        calc
          _ ≤ ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
              (xiPhysicalPrimeLogApertureEnd A k p)) ^ n‖ +
              ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
                (xiPhysicalPrimeLogApertureStart m p)) ^ n‖ := norm_sub_le _ _
          _ = 2 := by norm_num
      nlinarith [physicalPrimeEndpointWeight_pos p]
    _ = _ := by
      rw [xiPhysicalPrimeLogEndpointTotalWeight, Finset.mul_sum]

/-- Two-regime signed multipole law for physical endpoint moments. -/
theorem norm_xiPhysicalPrimeLogEndpointCircleMoment_le_min_dipole_total
    (P : Finset Nat.Primes) (A m k : ℝ) (n : ℕ) :
    ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ≤
      min ((n : ℝ) * xiPhysicalPrimeLogEndpointDipoleChordMass P A m k)
        (2 * xiPhysicalPrimeLogEndpointTotalWeight P) := by
  exact le_min
    (norm_xiPhysicalPrimeLogEndpointCircleMoment_le_nat_mul_dipoleChordMass P A m k n)
    (norm_xiPhysicalPrimeLogEndpointCircleMoment_le_two_mul_totalWeight P A m k n)

end

end RHTower
