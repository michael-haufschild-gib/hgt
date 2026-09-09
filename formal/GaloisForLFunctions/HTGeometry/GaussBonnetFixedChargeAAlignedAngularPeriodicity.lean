import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAAlignedAngularJets
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Field.Periodic

/-!
# Periodicity at every angular derivative order

Translation commutes with the totalized derivative, so every angular
jet remains periodic. No differentiability assumption is needed for
the periodicity induction, including coefficient states outside the
physical smooth domain.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAAlignedAngularCorrection_periodic (w φ : ℝ) (p : EGBAlignedForceState) :
    Function.Periodic (egbFixedChargeAAlignedAngularCorrection w φ p) (2 * Real.pi) := by
  intro ψ
  unfold egbFixedChargeAAlignedAngularCorrection
  rw [sin_add_two_pi, cos_add_two_pi]

theorem egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_periodic (w φ : ℝ) (p : EGBAlignedForceState) (n : ℕ) :
    Function.Periodic (iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ p)) (2 * Real.pi) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using egbFixedChargeAAlignedAngularCorrection_periodic w φ p
  | succ n ih =>
      rw [iteratedDeriv_succ]
      intro ψ
      have hf : (fun x => iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ p) (x + 2 * Real.pi)) =
          iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ p) := funext ih
      have h := deriv_comp_add_const (iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ p)) (2 * Real.pi) ψ
      rw [hf] at h
      exact h.symm

end GaloisForLFunctions.HTGeometry
