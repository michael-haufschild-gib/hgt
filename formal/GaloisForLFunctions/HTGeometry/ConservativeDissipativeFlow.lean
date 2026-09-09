import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

/-!
# Exact quadratic-energy flow and contraction

Applications of the operator split in Schaffer–Exl, arXiv:2609.04530.
-/

open scoped InnerProductSpace NNReal
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]


/-- The actual global flow for the quadratic potential `‖x‖²/2`. -/
def flow (A : E →L[ℝ] E) (B : E →L[ℝ] F) (x : E) (t : ℝ) : E :=
  NormedSpace.exp (t • generator A B) x

theorem hasDerivAt_flow (A : E →L[ℝ] E) (B : E →L[ℝ] F) (x : E) (t : ℝ) :
    HasDerivAt (flow A B x) (generator A B (flow A B x t)) t := by
  have hd := (hasDerivAt_exp_smul_const' (generator A B) t).clm_apply
    (hasDerivAt_const t x)
  convert hd using 1
  · rfl
  · simp only [flow, mul_apply_eq_comp, map_zero, add_zero]


/-- Exact continuous-time energy loss without an assumed trajectory. -/
theorem hasDerivAt_flow_energy (A : E →L[ℝ] E) (B : E →L[ℝ] F) (x : E) (t : ℝ) :
    HasDerivAt (fun s => ‖flow A B x s‖ ^ 2)
      (-2 * ‖B (flow A B x t)‖ ^ 2) t := by
  have h := (hasDerivAt_flow A B x t).norm_sq
  have hp := generator_power A B (flow A B x t)
  simp only [RCLike.re_to_real] at hp
  rw [hp] at h
  convert h using 1
  ring

/-- Energy is monotone along the constructed flow on the entire real time axis. -/
theorem flow_energy_antitone (A : E →L[ℝ] E) (B : E →L[ℝ] F) (x : E) :
    Antitone (fun t => ‖flow A B x t‖ ^ 2) := by
  apply antitone_of_deriv_nonpos
  · exact fun t => (hasDerivAt_flow_energy A B x t).differentiableAt
  · intro t
    rw [(hasDerivAt_flow_energy A B x t).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

/-- Finite-time energy cannot exceed its initial value at any nonnegative time. -/
theorem flow_energy_le_initial (A : E →L[ℝ] E) (B : E →L[ℝ] F) (x : E) (t : ℝ≥0) :
    ‖flow A B x t‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  simpa [flow] using flow_energy_antitone A B x t.coe_nonneg

/-- Differences evolve by the same flow, so the result controls trajectory separation. -/
theorem flow_sub (A : E →L[ℝ] E) (B : E →L[ℝ] F) (x y : E) (t : ℝ) :
    flow A B (x - y) t = flow A B x t - flow A B y t := by
  exact map_sub _ _ _

theorem flow_distance_sq_le (A : E →L[ℝ] E) (B : E →L[ℝ] F)
    (x y : E) (t : ℝ≥0) :
    dist (flow A B x t) (flow A B y t) ^ 2 ≤ dist x y ^ 2 := by
  simpa [dist_eq_norm, flow_sub] using flow_energy_le_initial A B (x - y) t

end
end GaloisForLFunctions.HTGeometry.SchafferExl
