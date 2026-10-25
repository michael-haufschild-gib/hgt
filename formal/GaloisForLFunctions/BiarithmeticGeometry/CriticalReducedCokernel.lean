import GaloisForLFunctions.BiarithmeticGeometry.CriticalCoefficientDomain
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The critical reduced cokernel is isometrically the complex line

The closure of the coefficient payment domain is the kernel of total
evaluation. Each class has the representative supported at zero with
that evaluation, and the evaluation bound proves its norm is minimal.
The resulting quotient isometry identifies the reduced cokernel exactly.
-/

noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

instance criticalTotalEvaluation_isClosed_ker :
    IsClosed (criticalTotalEvaluation.ker : Set CriticalCoefficientSpace) :=
  isClosed_singleton.preimage criticalTotalEvaluation.continuous

private theorem criticalEvaluation_quotient_norm_le (g : CriticalCoefficientSpace) :
    ‖(Submodule.Quotient.mk g : CriticalCoefficientSpace ⧸ criticalTotalEvaluation.ker)‖ ≤
      ‖criticalTotalEvaluation g‖ := by
  obtain ⟨z, hz, hmin, _⟩ := criticalTotalEvaluation_minimum_distance g
  have hclass :
      (Submodule.Quotient.mk g : CriticalCoefficientSpace ⧸ criticalTotalEvaluation.ker) =
        Submodule.Quotient.mk (g - z) := by
    apply (Submodule.Quotient.eq criticalTotalEvaluation.ker).mpr
    change criticalTotalEvaluation (g - (g - z)) = 0
    rwa [sub_sub_cancel]
  rw [hclass]
  exact (Submodule.Quotient.norm_mk_le criticalTotalEvaluation.ker (g - z)).trans_eq hmin

private theorem criticalEvaluation_le_quotient_norm (g : CriticalCoefficientSpace) :
    ‖criticalTotalEvaluation g‖ ≤
      ‖(Submodule.Quotient.mk g : CriticalCoefficientSpace ⧸ criticalTotalEvaluation.ker)‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨m, hm, hnorm⟩ := Submodule.Quotient.norm_mk_lt
    (S := criticalTotalEvaluation.ker) (Submodule.Quotient.mk g) hε
  have hker := (Submodule.Quotient.eq criticalTotalEvaluation.ker).mp hm
  change criticalTotalEvaluation (m - g) = 0 at hker
  rw [map_sub, sub_eq_zero] at hker
  rw [← hker]
  exact (norm_criticalTotalEvaluation_le m).trans hnorm.le

/-- The quotient norm is exactly the modulus of total coefficient evaluation. -/
theorem norm_criticalEvaluation_quotient_mk (g : CriticalCoefficientSpace) :
    ‖(Submodule.Quotient.mk g : CriticalCoefficientSpace ⧸ criticalTotalEvaluation.ker)‖ =
      ‖criticalTotalEvaluation g‖ :=
  le_antisymm (criticalEvaluation_quotient_norm_le g) (criticalEvaluation_le_quotient_norm g)

private def criticalEvaluationQuotientLinearEquiv :
    (CriticalCoefficientSpace ⧸ criticalTotalEvaluation.ker) ≃ₗ[ℂ] ℂ :=
  criticalTotalEvaluation.toLinearMap.quotKerEquivOfSurjective (by
    intro z
    exact ⟨lp.single 1 0 z, criticalTotalEvaluation_single z⟩)

/-- The evaluation quotient has its canonical isometric identification with the scalar field. -/
def criticalEvaluationQuotientIsometry :
    (CriticalCoefficientSpace ⧸ criticalTotalEvaluation.ker) ≃ₗᵢ[ℂ] ℂ where
  __ := criticalEvaluationQuotientLinearEquiv
  norm_map' := by
    intro q
    obtain ⟨g, rfl⟩ := criticalTotalEvaluation.ker.mkQ_surjective q
    change ‖criticalTotalEvaluation g‖ =
      ‖(Submodule.Quotient.mk g : CriticalCoefficientSpace ⧸ criticalTotalEvaluation.ker)‖
    exact (norm_criticalEvaluation_quotient_mk g).symm

/-- The cokernel after closing the actual critical coefficient payment domain. -/
abbrev CriticalReducedCoefficientCokernel :=
  CriticalCoefficientSpace ⧸ criticalCoefficientDomain.topologicalClosure

/-- The critical reduced cokernel is isometrically one complex dimension. -/
def criticalReducedCoefficientCokernelIsometry : CriticalReducedCoefficientCokernel ≃ₗᵢ[ℂ] ℂ :=
  (Submodule.quotLIEOfEq _ _ criticalCoefficientDomain_topologicalClosure).trans
    criticalEvaluationQuotientIsometry

theorem criticalReducedCoefficientCokernelIsometry_mk (g : CriticalCoefficientSpace) :
    criticalReducedCoefficientCokernelIsometry (Submodule.Quotient.mk g) =
      criticalTotalEvaluation g := rfl

instance : FiniteDimensional ℂ CriticalReducedCoefficientCokernel :=
  FiniteDimensional.of_injective criticalReducedCoefficientCokernelIsometry.toLinearMap
    criticalReducedCoefficientCokernelIsometry.injective

/-- The reduced obstruction index is one even when the unreduced algebraic defect is infinite. -/
theorem finrank_criticalReducedCoefficientCokernel :
    Module.finrank ℂ CriticalReducedCoefficientCokernel = 1 := by
  simpa only [Module.finrank_self] using
    criticalReducedCoefficientCokernelIsometry.toLinearEquiv.finrank_eq

end GaloisForLFunctions.BiarithmeticGeometry

