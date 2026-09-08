import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy
import GaloisForLFunctions.HTGeometry.TwoProjectionQuantumWalk
import GaloisForLFunctions.HTGeometry.DiscreteLiouvilleGreen
import GaloisForLFunctions.HTGeometry.ConstitutiveMutationalGenesis
import GaloisForLFunctions.HTGeometry.LeeYangTwoSpinCircle
/-!
# Quadratic cavity hierarchy in quantum walks, discrete energy, mutation, and Lee--Yang theory

The exact coefficient recurrence from arXiv:2608.14343, Eq. (S14), occurs in four
existing corpus constructions. These bridges identify the actual pre-existing
objects and transfer the recurrence's finite remainder and conserved energy.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
/-- The existing quantum-walk sine hierarchy is the cavity coefficient hierarchy. -/
theorem quadraticResponseCoeff_eq_unitarySineRecurrence
    {R : Type*} [Ring R] (X : R) (n : ℕ) :
    quadraticResponseCoeff (-X) 1 n = _root_.HTGeometry.unitarySineRecurrence X (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [quadraticResponseCoeff, _root_.HTGeometry.unitarySineRecurrence]
  | one => simp [quadraticResponseCoeff, _root_.HTGeometry.unitarySineRecurrence]
  | more n h0 h1 =>
      change quadraticResponseCoeff (-X) 1 (n + 2) =
        X * _root_.HTGeometry.unitarySineRecurrence X (n + 2) -
        _root_.HTGeometry.unitarySineRecurrence X (n + 1)
      rw [quadraticResponseCoeff_add_two, h0, h1]
      simp
/-- On every invertible phase, the hierarchy resolves the antisymmetric power exactly. -/
theorem quadraticResponseCoeff_unit_phase_difference
    {R : Type*} [Ring R] (U : Rˣ) (n : ℕ) :
    quadraticResponseCoeff (-((U : R) + (↑U⁻¹ : R))) 1 n *
        ((U : R) - (↑U⁻¹ : R)) = (U : R) ^ (n + 1) - (↑U⁻¹ : R) ^ (n + 1) := by
  rw [quadraticResponseCoeff_eq_unitarySineRecurrence]
  exact _root_.HTGeometry.unitarySineRecurrence_mul_sub_inversePair _ _
    (by simp) (by simp) _
/-- The undamped cavity coefficients solve the corpus's discrete Sturm--Liouville equation. -/
theorem quadraticResponseCoeff_isLGSolution (x : ℝ) :
    IsLGSolution (fun _ => 2 - 2 * x) (quadraticResponseCoeff (-(2 * x)) 1) := by
  intro n
  unfold lgDiff
  rw [show n + 1 + 1 = n + 2 by omega, quadraticResponseCoeff_add_two]
  ring
/-- The discrete Liouville--Green energy is exactly one throughout this coefficient hierarchy. -/
theorem lgEnergy_quadraticResponseCoeff (x : ℝ) (n : ℕ) :
    lgEnergy (fun _ => 2 - 2 * x) (quadraticResponseCoeff (-(2 * x)) 1) n = 1 := by
  induction n with
  | zero => simp [lgEnergy, lgDiff, lgProd]; ring
  | succ n ih =>
      have h := lgEnergy_succ_sub (quadraticResponseCoeff_isLGSolution x) n
      simp only [sub_self, zero_mul] at h
      linarith
/-- Rank-two mutation lineage is a fixed linear combination of the cavity recurrence. -/
theorem mutationalLineage_eq_quadraticResponseCoeff (n : ℕ) :
    mutationalLineage (n + 1) = quadraticResponseCoeff (-3 : ℤ) 1 (n + 1) -
      2 * quadraticResponseCoeff (-3 : ℤ) 1 n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [mutationalLineage, quadraticResponseCoeff]
  | one => simp [mutationalLineage, quadraticResponseCoeff]
  | more n h0 h1 =>
      have hl := mutationalLineage_recurrence (n + 1)
      have hc := quadraticResponseCoeff_add_two (-3 : ℤ) 1 n
      have hd := quadraticResponseCoeff_add_two (-3 : ℤ) 1 (n + 1)
      change mutationalLineage (n + 1 + 2) = _
      rw [hl, h0, h1]
      linear_combination -hd + 2 * hc
/-- The two-spin Lee--Yang diagonal has the same exact reciprocal expansion and finite remainder. -/
theorem leeYangTwoSpin_quadraticResponse_remainder (b : ℝ) (z : ℂ) (n : ℕ) :
    leeYangTwoSpin b z z *
        (∑ k ∈ Finset.range (n + 1), quadraticResponseCoeff (2 * (b : ℂ)) 1 k * z ^ k) =
      1 - quadraticResponseCoeff (2 * (b : ℂ)) 1 (n + 1) * z ^ (n + 1) +
        quadraticResponseCoeff (2 * (b : ℂ)) 1 n * z ^ (n + 2) := by
  have h := quadraticResponseCoeff_finite_remainder (2 * (b : ℂ)) 1 z n
  rw [leeYangTwoSpin_diagonal]
  convert h using 1 <;> ring
end
end GaloisForLFunctions.HTGeometry
