import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorMassPairings
import GaloisForLFunctions.HilbertMetric.Geometry.FubiniStudyPotential
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeZeroPhaseSensitivity

/-!
# Fubini–Study geometry of actual zero-coordinate phase orbits

Sector rotations preserve the projective potential and Levi metric.
The Levi energy of the negative-sector generator has an exact mass formula;
on a single zero coordinate it distinguishes critical-line and off-line
reflection behavior.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23
open HilbertMetric

private theorem phaseRotate_norm (u : Circle) (x : ZeroSpace) :
    ‖phaseRotate u x‖ = ‖x‖ := (phaseRotationEquiv u).norm_map x

/-- Sector rotations preserve the actual logarithmic projective potential. -/
theorem potential_phaseRotate (u : Circle) (x : ZeroSpace) :
    FubiniStudy.potential (phaseRotate u x) = FubiniStudy.potential x := by
  unfold FubiniStudy.potential FubiniStudy.denominator
  rw [phaseRotate_norm]

/-- The Levi metric is invariant under simultaneous sector rotation of point and tangent. -/
theorem levi_phaseRotate (u : Circle) (x v : ZeroSpace) :
    FubiniStudy.levi (phaseRotate u x) (phaseRotate u v) = FubiniStudy.levi x v := by
  simp only [FubiniStudy.levi_formula, FubiniStudy.denominator, phaseRotate_norm, inner_phaseRotate]

/-- The affine Levi energy of the reflection generator is an exact sector-mass expression. -/
theorem levi_negativePart (x : ZeroSpace) :
    FubiniStudy.levi x (negativePart x) = negativeMass x * (1 + positiveMass x) /
      (1 + ‖x‖ ^ 2) ^ 2 := by
  rw [FubiniStudy.levi_formula, inner_negativePart_eq_mass, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ negativeMass x from sq_nonneg _)]
  change negativeMass x / FubiniStudy.denominator x - negativeMass x ^ 2 / FubiniStudy.denominator x ^ 2 = _
  have hd := (FubiniStudy.denominator_pos x).ne'
  change _ = negativeMass x * (1 + positiveMass x) / FubiniStudy.denominator x ^ 2
  field_simp [hd]
  unfold FubiniStudy.denominator
  rw [← sector_mass_sum x]
  ring

/-- Strict Levi positivity detects a nontrivial negative reflection component. -/
theorem levi_negativePart_pos_iff (x : ZeroSpace) :
    0 < FubiniStudy.levi x (negativePart x) ↔ zeroReflection x ≠ x := by
  rw [FubiniStudy.levi_pos_iff]
  have hz : negativePart x = 0 ↔ zeroReflection x = x := by
    rw [negativePart, smul_eq_zero]
    simp only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or, sub_eq_zero]
    exact eq_comm
  exact not_congr hz

/-- At individual zero coordinates, the affine generator energy has exactly two values. -/
theorem levi_negativePart_zeroBasis (z : zetaZeroConfig.carrier) :
    FubiniStudy.levi (zeroBasis z) (negativePart (zeroBasis z)) =
      if (z : ℂ).re = 1 / 2 then 0 else 3 / 16 := by
  classical
  rw [levi_negativePart, norm_zeroBasis, (sector_masses_zeroBasis z).1,
    (sector_masses_zeroBasis z).2]
  by_cases hz : (z : ℂ).re = 1 / 2 <;> simp only [hz, if_true, if_false] <;> norm_num

#print axioms potential_phaseRotate
#print axioms levi_phaseRotate
#print axioms levi_negativePart
#print axioms levi_negativePart_pos_iff
#print axioms levi_negativePart_zeroBasis
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
