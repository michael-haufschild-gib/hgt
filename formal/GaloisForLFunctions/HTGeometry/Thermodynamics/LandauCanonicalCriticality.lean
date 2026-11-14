import GaloisForLFunctions.HTGeometry.TraceDynamicsLandauSchur
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Canonical criticality in the corpus Landau potential

The quartic normal form of arXiv:2611.16364, equation (5.9), occurs as a
scalar slice of the existing two-channel Landau energy. Completing the
square determines its minimum for every mass parameter. At zero mass,
the cubic field law has one global minimizer and an exact inverse-stiffness
scaling identity. These are statements about the exact quartic model.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.Thermodynamics
open TraceDynamics

def landauScalarMinimum (u r : ℝ) : ℝ := -(min r 0) ^ 2 / (4 * Real.exp u ^ 2)
def landauEquilibriumSquare (u r : ℝ) : ℝ := -(min r 0) / (2 * Real.exp u ^ 2)

theorem landauScalar_slice (u r x : ℝ) :
    landauPotential r 0 u 0 0 x 0 = r * x ^ 2 + Real.exp u ^ 2 * x ^ 4 := by
  simp [landauPotential, landauQuartic]

/-- The exact energy gap splits into two nonnegative terms in both phases. -/
theorem landauScalar_gap (u r x : ℝ) :
    landauPotential r 0 u 0 0 x 0 - landauScalarMinimum u r =
      Real.exp u ^ 2 * (x ^ 2 + min r 0 / (2 * Real.exp u ^ 2)) ^ 2 + max r 0 * x ^ 2 := by
  rw [landauScalar_slice]
  unfold landauScalarMinimum
  by_cases h : r ≤ 0
  · rw [min_eq_left h, max_eq_right h]
    field_simp
    ring
  · have h' : 0 ≤ r := le_of_not_ge h
    rw [min_eq_right h', max_eq_left h']
    ring

theorem landauScalar_global_lower_bound (u r x : ℝ) :
    landauScalarMinimum u r ≤ landauPotential r 0 u 0 0 x 0 := by
  apply sub_nonneg.mp
  rw [landauScalar_gap]
  positivity

theorem landauEquilibriumSquare_nonneg (u r : ℝ) : 0 ≤ landauEquilibriumSquare u r := by
  unfold landauEquilibriumSquare
  exact div_nonneg (neg_nonneg.mpr (min_le_right _ _)) (by positivity)

/-- The global minimizing amplitudes are completely classified, including zero mass. -/
theorem landauScalar_minimizers (u r x : ℝ) :
    landauPotential r 0 u 0 0 x 0 = landauScalarMinimum u r ↔
      x ^ 2 = landauEquilibriumSquare u r := by
  rw [← sub_eq_zero, landauScalar_gap]
  have h₁ : 0 ≤ Real.exp u ^ 2 * (x ^ 2 + min r 0 / (2 * Real.exp u ^ 2)) ^ 2 := by
    positivity
  have h₂ : 0 ≤ max r 0 * x ^ 2 := by positivity
  constructor
  · intro h
    have hz : Real.exp u ^ 2 * (x ^ 2 + min r 0 / (2 * Real.exp u ^ 2)) ^ 2 = 0 := by
      linarith only [h, h₁, h₂]
    have hs := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (Real.exp_ne_zero u))
    have hs' := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hs
    unfold landauEquilibriumSquare
    rw [neg_div]
    linarith only [hs']
  · intro h
    have hs : x ^ 2 + min r 0 / (2 * Real.exp u ^ 2) = 0 := by
      unfold landauEquilibriumSquare at h
      rw [neg_div] at h
      linarith only [h]
    rw [hs, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
    by_cases hr : r ≤ 0
    · rw [max_eq_right hr, zero_mul]
    · have hr' : 0 ≤ r := le_of_not_ge hr
      have hx : x ^ 2 = 0 := by simpa [landauEquilibriumSquare, min_eq_right hr'] using h
      rw [hx, mul_zero]

/-- Both square-root amplitudes attain the proved variational floor. -/
theorem landauScalar_minimum_attained (u r : ℝ) :
    landauPotential r 0 u 0 0 (Real.sqrt (landauEquilibriumSquare u r)) 0 = landauScalarMinimum u r ∧
      landauPotential r 0 u 0 0 (-Real.sqrt (landauEquilibriumSquare u r)) 0 = landauScalarMinimum u r := by
  constructor
  · exact (landauScalar_minimizers u r _).mpr (Real.sq_sqrt (landauEquilibriumSquare_nonneg u r))
  · apply (landauScalar_minimizers u r _).mpr
    rw [neg_sq, Real.sq_sqrt (landauEquilibriumSquare_nonneg u r)]

/-- On the disordered side the sole minimizer is zero. -/
theorem landauScalar_nonnegative_mass_minimizer (u a x : ℝ) :
    landauPotential (a ^ 2) 0 u 0 0 x 0 = landauScalarMinimum u (a ^ 2) ↔ x = 0 := by
  rw [landauScalar_minimizers]
  simp [landauEquilibriumSquare, min_eq_right (sq_nonneg a)]

/-- Squared phase separation is exactly proportional to distance below zero mass. -/
theorem landauScalar_ordered_gap_squared (u a : ℝ) :
    (Real.sqrt (landauEquilibriumSquare u (-Real.exp a)) -
      (-Real.sqrt (landauEquilibriumSquare u (-Real.exp a)))) ^ 2 =
        2 * Real.exp a / Real.exp u ^ 2 := by
  rw [show (Real.sqrt (landauEquilibriumSquare u (-Real.exp a)) -
      (-Real.sqrt (landauEquilibriumSquare u (-Real.exp a)))) ^ 2 =
        4 * Real.sqrt (landauEquilibriumSquare u (-Real.exp a)) ^ 2 by ring,
    Real.sq_sqrt (landauEquilibriumSquare_nonneg u (-Real.exp a))]
  unfold landauEquilibriumSquare
  rw [min_eq_left (neg_nonpos.mpr (Real.exp_pos a).le)]
  ring

def criticalLandauField (u m : ℝ) : ℝ := 4 * Real.exp u ^ 2 * m ^ 3
def criticalLandauPotential (u h x : ℝ) : ℝ := landauPotential 0 0 u 0 0 x 0 - h * x

/-- Cubic field matching yields an exact globally nonnegative energy gap. -/
theorem criticalLandau_gap (u m x : ℝ) :
    criticalLandauPotential u (criticalLandauField u m) x -
      criticalLandauPotential u (criticalLandauField u m) m =
        Real.exp u ^ 2 * (x - m) ^ 2 * ((x + m) ^ 2 + 2 * m ^ 2) := by
  unfold criticalLandauPotential criticalLandauField
  rw [landauScalar_slice, landauScalar_slice]
  ring

theorem criticalLandau_global_lower_bound (u m x : ℝ) :
    criticalLandauPotential u (criticalLandauField u m) m ≤
      criticalLandauPotential u (criticalLandauField u m) x := by
  apply sub_nonneg.mp
  rw [criticalLandau_gap]
  positivity

/-- The critical field has exactly one equilibrium, including at zero field. -/
theorem criticalLandau_unique_minimizer (u m x : ℝ) :
    criticalLandauPotential u (criticalLandauField u m) x =
        criticalLandauPotential u (criticalLandauField u m) m ↔ x = m := by
  rw [← sub_eq_zero, criticalLandau_gap]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | hright
    · have hs := (mul_eq_zero.mp hleft).resolve_left (pow_ne_zero 2 (Real.exp_ne_zero u))
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hs)
    · have hm2 : m ^ 2 = 0 := by nlinarith only [hright, sq_nonneg (x + m), sq_nonneg m]
      have hm : m = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hm2
      subst m
      simpa using hright
  · intro h
    rw [h, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul]

theorem criticalLandauField_hasDerivAt (u m : ℝ) :
    HasDerivAt (criticalLandauField u) (12 * Real.exp u ^ 2 * m ^ 2) m := by
  apply (((hasDerivAt_id m).pow 3).const_mul (4 * Real.exp u ^ 2)).congr_deriv
  dsimp
  ring

/-- The cubic equation gives the exact two-thirds inverse-stiffness scaling law. -/
theorem criticalLandau_inverse_stiffness_scaling (u v : ℝ) :
    (deriv (criticalLandauField u) (Real.exp v))⁻¹ ^ 3 *
      criticalLandauField u (Real.exp v) ^ 2 = 1 / (108 * Real.exp u ^ 2) := by
  rw [(criticalLandauField_hasDerivAt u (Real.exp v)).deriv]
  unfold criticalLandauField
  field_simp
  ring

#print axioms landauScalar_minimizers
#print axioms landauScalar_minimum_attained
#print axioms landauScalar_ordered_gap_squared
#print axioms criticalLandau_unique_minimizer
#print axioms criticalLandau_inverse_stiffness_scaling

end GaloisForLFunctions.HTGeometry.Thermodynamics
