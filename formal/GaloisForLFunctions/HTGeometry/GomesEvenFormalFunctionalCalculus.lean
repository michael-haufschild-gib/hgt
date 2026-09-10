import GaloisForLFunctions.HTGeometry.GomesPolynomialReflectionJointCommutant
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# The surviving joint symmetries are precisely formal functions of D squared

The scalar two-chain operator is exactly the existing formal calculus applied to
F(X²). Thus the matrix classification identifies a concrete subalgebra of the full
first-derivative commutant, with the entire formal series retained.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- Substitution of X² into any formal symbol gives a scalar two-chain matrix. -/
theorem gomesFormalSeriesDerivativePowerMatrixHom_expand_two (F : PowerSeries K) :
    gomesFormalSeriesDerivativePowerMatrixHom K 2 (PowerSeries.expand 2 (Nat.succ_ne_zero 1) F) =
      Matrix.scalar (Fin 2) F := by
  have he : gomesFormalCoefficientResidue K 2 0
      (PowerSeries.expand 2 (Nat.succ_ne_zero 1) F) = F := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.mk _) = _
    rw [PowerSeries.coeff_mk]
    simpa only [Fin.val_zero, Nat.add_zero, Nat.mul_comm] using
      PowerSeries.coeff_expand_mul 2 (Nat.succ_ne_zero 1) F n
  have ho : gomesFormalCoefficientResidue K 2 1
      (PowerSeries.expand 2 (Nat.succ_ne_zero 1) F) = 0 := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.mk _) = _
    rw [PowerSeries.coeff_mk, map_zero]
    apply PowerSeries.coeff_expand_of_not_dvd
    simp
  rw [gomesFormalSeriesDerivativePowerMatrixHom_two, he, ho]
  apply Matrix.ext
  intro i j
  revert i j
  simp [Fin.forall_fin_two, Matrix.scalar_apply]

/-- The shared chain-scalar operator is precisely the formal function F(D²). -/
theorem gomesEvenFormalPolynomialOperator_eq_expanded (F : PowerSeries K) :
    gomesEvenFormalPolynomialOperator K F =
      gomesFormalSeriesPolynomialOperator K (PowerSeries.expand 2 (Nat.succ_ne_zero 1) F) := by
  have h := gomesFormalSeriesDerivativePowerMatrixHom_expand_two K F
  change gomesPolynomialDerivativePowerCommutantEquiv K 2
    (gomesFormalSeriesDerivativePowerHom K 2 (PowerSeries.expand 2 (Nat.succ_ne_zero 1) F)) = _ at h
  have he := congrArg (gomesPolynomialDerivativePowerCommutantEquiv K 2).symm h
  rw [AlgEquiv.symm_apply_apply] at he
  exact (congrArg Subtype.val he).symm

/-- Exactly the formal functions of D² commute with D and an arbitrary affine reflection. -/
theorem gomesPolynomialDerivativeReflection_joint_iff_even_series
    (c : K) (E : Module.End K K[X]) :
    (Commute E Polynomial.derivative ∧ Commute E (gomesPolynomialReflectionEnd K c)) ↔
      ∃ F : PowerSeries K,
        E = gomesFormalSeriesPolynomialOperator K (PowerSeries.expand 2 (Nat.succ_ne_zero 1) F) := by
  rw [gomesPolynomialDerivativeReflection_joint_commutant]
  simp only [gomesEvenFormalPolynomialOperator_eq_expanded]

end GaloisForLFunctions.HTGeometry
