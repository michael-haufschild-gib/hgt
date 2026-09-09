import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

/-!
# Unconditional resolvents and exact discrete energy balances

The Schaffer–Exl split (arXiv:2609.04530) gives a coercive identity shift
for every nonnegative step size on real or complex Hilbert spaces.
Backward Euler and Cayley midpoint updates therefore exist without a
step-size restriction. Their exact energy identities distinguish physical
observation damping from the additional numerical damping of backward Euler.
-/
open scoped InnerProductSpace NNReal Ring
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Implicit shift of an unrestricted conservative–dissipative generator. -/
def implicitShift (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) : E →L[𝕜] E :=
  1 - ((t : ℝ) : 𝕜) • generator A B

/-- The identity shift has coercivity one for every nonnegative step size. -/
theorem implicitShift_power (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    RCLike.re ⟪x, implicitShift A B t x⟫_𝕜 = ‖x‖ ^ 2 + (t : ℝ) * ‖B x‖ ^ 2 := by
  simp only [implicitShift, sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
    inner_smul_right, map_sub, inner_self_eq_norm_sq, RCLike.re_ofReal_mul, generator_power]
  ring

/-- Every implicit shift is invertible, with no step-size or spectral hypothesis. -/
theorem implicitShift_isUnit (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) :
    IsUnit (implicitShift A B t) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c := 1) zero_lt_one
  intro x
  have hp := implicitShift_power A B t x
  have hn := RCLike.re_le_norm (⟪implicitShift A B t x, x⟫_𝕜)
  rw [inner_re_symm] at hn
  rw [hp] at hn
  simp only [NNReal.coe_one, mul_one]
  exact (le_add_of_nonneg_right (mul_nonneg t.coe_nonneg (sq_nonneg _))).trans hn

/-- The genuine inverse update, defined for arbitrary nonnegative step size. -/
def implicitStep (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) : E →L[𝕜] E :=
  (implicitShift A B t)⁻¹ʳ

theorem implicitShift_implicitStep (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    implicitShift A B t (implicitStep A B t x) = x := by
  have h := congrArg (fun C : E →L[𝕜] E => C x)
    (Ring.mul_inverse_cancel (implicitShift A B t) (implicitShift_isUnit A B t))
  simpa only [implicitStep, mul_apply_eq_comp, one_apply_eq_self] using h

/-- The input is exactly the implicit output minus its generator displacement. -/
theorem implicitStep_equation (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    implicitStep A B t x - ((t : ℝ) : 𝕜) • generator A B (implicitStep A B t x) = x :=
  implicitShift_implicitStep A B t x

/-- Backward Euler loses physical damping plus a distinct nonnegative numerical term. -/
theorem implicitStep_energy (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    ‖implicitStep A B t x‖ ^ 2 + 2 * (t : ℝ) * ‖B (implicitStep A B t x)‖ ^ 2 +
      (t : ℝ) ^ 2 * ‖generator A B (implicitStep A B t x)‖ ^ 2 = ‖x‖ ^ 2 := by
  have he := congrArg (fun y : E => ‖y‖ ^ 2) (implicitStep_equation A B t x)
  rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, generator_power,
    norm_smul, RCLike.norm_ofReal, abs_of_nonneg t.coe_nonneg] at he
  nlinarith [he]

/-- Backward Euler is contractive for arbitrary step size. -/
theorem implicitStep_norm_le (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    ‖implicitStep A B t x‖ ≤ ‖x‖ := by
  have he := implicitStep_energy A B t x
  have h1 := mul_nonneg t.coe_nonneg (sq_nonneg ‖B (implicitStep A B t x)‖)
  have h2 := mul_nonneg (sq_nonneg (t : ℝ)) (sq_nonneg ‖generator A B (implicitStep A B t x)‖)
  nlinarith [norm_nonneg x, norm_nonneg (implicitStep A B t x)]

/-- The Cayley midpoint update uses the same unconditional inverse. -/
def cayleyStep (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) : E →L[𝕜] E :=
  (1 + ((t : ℝ) : 𝕜) • generator A B) * implicitStep A B t

theorem cayleyStep_apply (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    cayleyStep A B t x = implicitStep A B t x +
      ((t : ℝ) : 𝕜) • generator A B (implicitStep A B t x) := by
  simp only [cayleyStep, mul_apply_eq_comp, add_apply, smul_apply, one_apply_eq_self]

/-- Exact midpoint energy balance: only the physical observation damping remains. -/
theorem cayleyStep_energy (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    ‖cayleyStep A B t x‖ ^ 2 + 4 * (t : ℝ) * ‖B (implicitStep A B t x)‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [cayleyStep_apply, norm_add_sq (𝕜 := 𝕜), inner_smul_right,
    RCLike.re_ofReal_mul, generator_power, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg t.coe_nonneg]
  nlinarith [implicitStep_energy A B t x]

/-- Cayley evolution is contractive at every nonnegative step size. -/
theorem cayleyStep_norm_le (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    ‖cayleyStep A B t x‖ ≤ ‖x‖ := by
  have he := cayleyStep_energy A B t x
  have hn := mul_nonneg t.coe_nonneg (sq_nonneg ‖B (implicitStep A B t x)‖)
  nlinarith [norm_nonneg x, norm_nonneg (cayleyStep A B t x)]

/-- Exact discrete midpoint equation, with full time step `2t`. -/
theorem cayleyStep_midpoint (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    cayleyStep A B t x - x = ((t : ℝ) : 𝕜) • generator A B (cayleyStep A B t x + x) := by
  let y := implicitStep A B t x
  have hx : y - ((t : ℝ) : 𝕜) • generator A B y = x := implicitStep_equation A B t x
  have hc : cayleyStep A B t x = y + ((t : ℝ) : 𝕜) • generator A B y := cayleyStep_apply A B t x
  rw [hc]
  have hs : y + ((t : ℝ) : 𝕜) • generator A B y + x = y + y := by rw [← hx]; abel
  rw [hs, map_add, smul_add, ← hx]
  abel

/-- Operator norm contractivity of the discrete midpoint step. -/
theorem cayleyStep_opNorm_le_one (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) :
    ‖cayleyStep A B t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using cayleyStep_norm_le A B t x

/-- The lossless midpoint states are precisely the observation kernel at the implicit midpoint. -/
theorem cayleyStep_energy_eq_iff (A : E →L[𝕜] E) (B : E →L[𝕜] F) (t : ℝ≥0) (x : E) :
    ‖cayleyStep A B t x‖ ^ 2 = ‖x‖ ^ 2 ↔ t = 0 ∨ B (implicitStep A B t x) = 0 := by
  have he := cayleyStep_energy A B t x
  have hh : ‖cayleyStep A B t x‖ ^ 2 = ‖x‖ ^ 2 ↔
      (t : ℝ) * ‖B (implicitStep A B t x)‖ ^ 2 = 0 := by constructor <;> intro h <;> nlinarith
  rw [hh, mul_eq_zero, sq_eq_zero_iff, norm_eq_zero, NNReal.coe_eq_zero]

/-- Purely conservative midpoint updates preserve quadratic energy exactly. -/
theorem cayleyStep_conservative_energy (A : E →L[𝕜] E) (t : ℝ≥0) (x : E) :
    ‖cayleyStep A (0 : E →L[𝕜] F) t x‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa using cayleyStep_energy A (0 : E →L[𝕜] F) t x

end
end GaloisForLFunctions.HTGeometry.SchafferExl
