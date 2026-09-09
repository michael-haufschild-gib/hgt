import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import GaloisForLFunctions.HTGeometry.ConstraintLaplacian

/-!
# Constraint observers as conservative–dissipative dynamics

Applications of the operator split in Schaffer–Exl, arXiv:2609.04530.
-/

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {ι : Type*} [Fintype ι]
  (U : ι → Submodule 𝕜 E) [∀ i, (U i).HasOrthogonalProjection]

/-- The corpus constraint Laplacian is the observation damping of the latent-energy split. -/
theorem damping_constraintDefect : damping (constraintDefect U) = constraintLaplacian U := by
  rw [damping, adjoint_constraintDefect, constraintLaplacian_eq_comp]

/-- Adding arbitrary conservative mixing leaves the total constraint-defect loss exact. -/
theorem constraint_generator_power (A : E →L[𝕜] E) (x : E) :
    RCLike.re ⟪x, (conservative A - constraintLaplacian U) x⟫_𝕜 =
      -constraintEnergy U x := by
  rw [← damping_constraintDefect]
  exact (generator_power A (constraintDefect U) x).trans
    (congrArg Neg.neg (norm_sq_constraintDefect U x))

/-- The lossless sector consists exactly of states accepted by every constraint. -/
theorem constraint_generator_lossless_iff (A : E →L[𝕜] E) (x : E) :
    RCLike.re ⟪x, (conservative A - constraintLaplacian U) x⟫_𝕜 = 0 ↔
      ∀ i, x ∈ U i := by
  rw [constraint_generator_power, neg_eq_zero, constraintEnergy_eq_zero_iff]

/-- Stationarity requires both joint constraint satisfaction and conservative stationarity. -/
theorem constraint_generator_equilibrium_iff (A : E →L[𝕜] E) (x : E) :
    (conservative A - constraintLaplacian U) x = 0 ↔
      (∀ i, x ∈ U i) ∧ conservative A x = 0 := by
  rw [← damping_constraintDefect]
  change generator A (constraintDefect U) x = 0 ↔ _
  rw [generator_eq_zero_iff]
  have h : constraintDefect U x = 0 ↔ ∀ i, x ∈ U i := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, norm_sq_constraintDefect, constraintEnergy_eq_zero_iff]
  rw [h]

/-- A precise sum-of-squares dissipation inequality for the existing constraint system. -/
theorem constraint_generator_power_nonpos (A : E →L[𝕜] E) (x : E) :
    RCLike.re ⟪x, (conservative A - constraintLaplacian U) x⟫_𝕜 ≤ 0 := by
  rw [constraint_generator_power]
  exact neg_nonpos.mpr (constraintEnergy_nonneg U x)

end
end GaloisForLFunctions.HTGeometry.SchafferExl
