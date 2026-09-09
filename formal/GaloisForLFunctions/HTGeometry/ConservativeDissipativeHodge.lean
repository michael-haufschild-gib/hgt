import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.Energy

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
open HodgeEdgeCochain
variable {ι : Type*} [Fintype ι]
  (W : Submodule ℝ (EuclideanSpace ℝ ι))
  (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)

/-- A concrete nonlinear Hodge interaction built from unconstrained operator coefficients. -/
def hodgeInteraction : W →L[ℝ] W →L[ℝ] W :=
  projectedInteraction W (anticommutator (diagOp ι) (conservative A))

/-- The paper's skew construction discharges the existing Hodge cancellation premise. -/
theorem hodgeInteraction_cancelling : IsCancelling (hodgeInteraction W A) := by
  apply isCancelling_diagAnticommutatorInteraction
  intro x y
  calc
    ⟪conservative A x, y⟫_ℝ = ⟪x, (conservative A).adjoint y⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_right _ x y).symm
    _ = -⟪x, conservative A y⟫_ℝ := by
      rw [adjoint_conservative]
      simp

/-- Total power of the existing nonlinear two-field system is exactly two observation losses. -/
theorem hodge_total_power (L : W →L[ℝ] W) (u h : W) (nu eta : ℝ) :
    ⟪u, velocityField (damping L) (hodgeInteraction W A) (nu ^ 2) 0 u h⟫_ℝ +
      ⟪h, magneticField (damping L) (hodgeInteraction W A) (eta ^ 2) 0 u h⟫_ℝ =
      -nu ^ 2 * ‖L u‖ ^ 2 - eta ^ 2 * ‖L h‖ ^ 2 := by
  have hc := (hodgeInteraction_cancelling W A).energy_cancel u h
  simp only [inner_sub_left] at hc
  simp only [velocityField, magneticField, add_zero, inner_add_right, inner_sub_right,
    inner_neg_right, real_inner_smul_right]
  have hu := damping_power L u
  have hh := damping_power L h
  simp only [RCLike.re_to_real] at hu hh
  rw [hu, hh]
  rw [real_inner_comm u, real_inner_comm u, real_inner_comm h, real_inner_comm h] at hc
  nlinarith

/-- Arbitrary nonlinear coupling cannot overcome the two damping channels. -/
theorem hodge_total_power_nonpos (L : W →L[ℝ] W) (u h : W) (nu eta : ℝ) :
    ⟪u, velocityField (damping L) (hodgeInteraction W A) (nu ^ 2) 0 u h⟫_ℝ +
      ⟪h, magneticField (damping L) (hodgeInteraction W A) (eta ^ 2) 0 u h⟫_ℝ ≤ 0 := by
  rw [hodge_total_power]
  nlinarith [mul_nonneg (sq_nonneg nu) (sq_nonneg ‖L u‖),
    mul_nonneg (sq_nonneg eta) (sq_nonneg ‖L h‖)]

/-- External forcing adds precisely its power pairing, retaining the exact dissipation budget. -/
theorem hodge_forced_power (L : W →L[ℝ] W) (u h f g : W) (nu eta : ℝ) :
    ⟪u, velocityField (damping L) (hodgeInteraction W A) (nu ^ 2) f u h⟫_ℝ +
      ⟪h, magneticField (damping L) (hodgeInteraction W A) (eta ^ 2) g u h⟫_ℝ =
      -nu ^ 2 * ‖L u‖ ^ 2 - eta ^ 2 * ‖L h‖ ^ 2 + ⟪u, f⟫_ℝ + ⟪h, g⟫_ℝ := by
  have hz := hodge_total_power W A L u h nu eta
  simp only [velocityField, magneticField, add_zero, inner_add_right] at hz ⊢
  linarith

end
end GaloisForLFunctions.HTGeometry.SchafferExl
