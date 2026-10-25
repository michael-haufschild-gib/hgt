import GaloisForLFunctions.ArithmeticDefectRigidity.PaidWienerKernelsAnnihilateTheCofactorLimit

/-!
# Paid annihilation in the actual escape module

The full source-to-module comparison is supplied by Arithmetic Defect Rigidity. These
programme interfaces retain the admission alternative and the actual source obstruction hull.
-/

noncomputable section
open GaloisForLFunctions
open BezoutValuationIncidence ArithmeticContinuationAndCriticalEnergy
open ArithmeticCompensationTheory ArithmeticOrientationTheory ArithmeticDefectRigidity
open ArithmeticDefectRigidity.CofactorLimit
open RHTower

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Every actual common Gram limit is annihilated by the full repairing ideal on escape. -/
theorem admits_or_all_actual_annihilators (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ L : ActualCofactorLimit ε,
      paidIdeal (pmPowerDampedRealWeight ε)
        (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) ≤
          ActualCofactorLimit.annihilator L := by
  by_cases h : Admits dampedMobiusEnergy ε
  · exact Or.inl h
  · exact Or.inr fun L =>
      (ActualCofactorLimit.admits_or_paidIdeal_le_annihilator L).resolve_left h

/-- Every actual escape module has a nonempty subhull of the source obstruction hull. -/
theorem admits_or_all_actual_moduleHulls (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ L : ActualCofactorLimit ε,
      (ActualCofactorLimit.moduleHull L).Nonempty ∧
        ActualCofactorLimit.moduleHull L ⊆ obstructionHull (pmPowerDampedRealWeight ε)
          (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) := by
  by_cases h : Admits dampedMobiusEnergy ε
  · exact Or.inl h
  · exact Or.inr fun L =>
      (ActualCofactorLimit.admits_or_moduleHull_nonempty_subset L).resolve_left h

/-- Every full repairing kernel annihilates the chosen actual cofactor module on escape. -/
theorem admits_or_paidIdeal_le_annihilator (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      paidIdeal (pmPowerDampedRealWeight ε)
        (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) ≤
          annihilator ε :=
  CofactorLimit.admits_or_paidIdeal_le_annihilator ε

/-- The actual escape module has a nonempty hull inside the source obstruction hull. -/
theorem admits_or_moduleHull_inside_obstructionHull (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      (moduleHull ε).Nonempty ∧ moduleHull ε ⊆
        obstructionHull (pmPowerDampedRealWeight ε)
          (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) :=
  CofactorLimit.admits_or_moduleHull_nonempty_subset ε

end GaloisForLFunctions.BiarithmeticGeometry
