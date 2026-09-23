import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

/-!
# Conservative–dissipative nonlinear laws

Applications of Schaffer–Exl, arXiv:2609.04530, to constructed operators
and the existing mathematical objects used below.
-/

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A concave quadratic energy reverses the sign of the negative identity generator. -/
theorem concave_quadratic_field (x : E) :
    generator (0 : E →L[ℝ] E) (ContinuousLinearMap.id ℝ E) (-x) = x := by
  simp [generator, conservative, damping]

omit [CompleteSpace E] in
/-- Explicit growing solution of the concave quadratic gradient dynamics. -/
theorem hasDerivAt_concave_quadratic_orbit (x : E) (t : ℝ) :
    HasDerivAt (fun s => Real.exp s • x) (Real.exp t • x) t := by
  simpa using (Real.hasDerivAt_exp t).smul_const x

omit [CompleteSpace E] in
/-- Its energy still decreases: dissipation alone does not control state size. -/
theorem hasDerivAt_concave_quadratic_energy (x : E) (t : ℝ) :
    HasDerivAt (fun s => -(‖Real.exp s • x‖ ^ (2 : ℕ)) / 2)
      (-‖Real.exp t • x‖ ^ (2 : ℕ)) t := by
  have h := ((hasDerivAt_concave_quadratic_orbit x t).norm_sq.neg).div_const 2
  have hi : ⟪Real.exp t • x, Real.exp t • x⟫_ℝ = ‖Real.exp t • x‖ ^ (2 : ℕ) := by
    simp
  rw [hi] at h
  convert h using 1 <;> first | rfl | ring

/-- A concrete nonzero initial state moves strictly farther from equilibrium at positive times. -/
theorem concave_quadratic_state_grows (s : ℝ) :
    dist (Real.exp (1 + s ^ (2 : ℕ))) 0 > dist (1 : ℝ) 0 := by
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one]
  exact Real.one_lt_exp_iff.mpr (by nlinarith [sq_nonneg s])

end
end GaloisForLFunctions.HTGeometry.SchafferExl
