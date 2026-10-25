import GaloisForLFunctions.ArithmeticDefectRigidity.PaidWienerKernelsAnnihilateTheCofactorLimit
import GaloisForLFunctions.ArithmeticOrientationTheory.TheOperatorHullOfAWienerAction

/-!
# The norm-bounded spectrum of the actual cofactor action

Every actual common limit has a nonempty operator hull. On escape it lies in
the arithmetic obstruction hull. Its coordinates obey the exact dilation
norms; in finite dimension the entire module hull satisfies these bounds.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

open ArithmeticOrientationTheory
open _root_.RHTower GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

/-- The actual cofactor action has a nonempty norm-bounded spectral hull. -/
theorem operatorHull_nonempty {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    (ArithmeticOrientationTheory.operatorHull (wienerRepresentation L)).Nonempty := by
  letI : Nontrivial (Hilbert L) := ⟨⟨vector L 1, 0, vector_one_ne_zero L⟩⟩
  exact ArithmeticOrientationTheory.operatorHull_nonempty (wienerRepresentation L)

theorem operatorHull_subset_moduleHull {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    ArithmeticOrientationTheory.operatorHull (wienerRepresentation L) ⊆ moduleHull L :=
  ArithmeticOrientationTheory.operatorHull_subset_annihilatorHull (wienerRepresentation L)

/-- Each actual module's norm-bounded Bohr coordinates satisfy its exact operator bound. -/
theorem operatorHull_coordinate_le {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) {ω : BohrPoint}
    (hω : ω ∈ ArithmeticOrientationTheory.operatorHull (wienerRepresentation L)) (p : ℕ+) :
    ‖ω.ω p‖ ≤ Real.sqrt (p : ℝ) * ‖dilation L p‖ := by
  simpa only [wienerRepresentation_pointMass, Real.sqrt_eq_rpow] using
    norm_coordinate_le_operatorHull (wienerRepresentation L) hω p

/-- Escape gives a nonempty norm-bounded spectral subset of the actual obstruction hull. -/
theorem admits_or_operatorHull_nonempty_subset {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      (ArithmeticOrientationTheory.operatorHull (wienerRepresentation L)).Nonempty ∧
        ArithmeticOrientationTheory.operatorHull (wienerRepresentation L) ⊆
          obstructionHull (pmPowerDampedRealWeight ε)
            (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) := by
  rcases admits_or_moduleHull_subset_obstructionHull L with h | h
  · exact Or.inl h
  · exact Or.inr ⟨operatorHull_nonempty L, (operatorHull_subset_moduleHull L).trans h⟩

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

open ArithmeticOrientationTheory

/-- In the finite-dimensional branch the entire module hull obeys operator-norm bounds. -/
theorem operatorHull_eq_moduleHull_of_finite {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    [FiniteDimensional ℂ (Hilbert L)] :
    ArithmeticOrientationTheory.operatorHull (wienerRepresentation L) = moduleHull L := by
  letI : Nontrivial (Hilbert L) := ⟨⟨vector L 1, 0, vector_one_ne_zero L⟩⟩
  exact operatorHull_eq_annihilatorHull_of_isClosed_range (wienerRepresentation L)
    (wienerRepresentation L).range.toSubmodule.closed_of_finiteDimensional

theorem moduleHull_coordinate_le_of_finite {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    [FiniteDimensional ℂ (Hilbert L)] {ω : BohrPoint} (hω : ω ∈ moduleHull L) (p : ℕ+) :
    ‖ω.ω p‖ ≤ Real.sqrt (p : ℝ) * ‖dilation L p‖ := by
  apply operatorHull_coordinate_le L _ p
  rwa [operatorHull_eq_moduleHull_of_finite]

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit
