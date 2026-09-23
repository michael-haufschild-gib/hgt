import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

/-!
# Conservative–dissipative gauge laws

Applications of Schaffer–Exl, arXiv:2609.04530, to constructed operators
and the existing mathematical objects used below.
-/

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Simultaneous scaling of the skew coefficient and damping factor preserves structure. -/
theorem generator_scale (A : E →L[ℝ] E) (B : E →L[ℝ] F) (c : ℝ) :
    generator (c ^ (2 : ℕ) • A) (c • B) = c ^ (2 : ℕ) • generator A B := by
  ext x
  simp [generator, conservative, damping, ContinuousLinearMap.adjoint.map_smulₛₗ,
    smul_sub, smul_smul, pow_two]

/-- Positive potential-scale gauge with an unconstrained real logarithmic parameter. -/
theorem force_scale_gauge (A : E →L[ℝ] E) (B : E →L[ℝ] F) (s : ℝ) (g : E) :
    generator ((Real.exp (-s)) ^ (2 : ℕ) • A) (Real.exp (-s) • B)
      ((Real.exp s) ^ (2 : ℕ) • g) = generator A B g := by
  rw [generator_scale]
  simp only [smul_apply, map_smul, smul_smul]
  rw [← mul_pow, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_pow, one_smul]

/-- The numeric energy-loss scale changes even though the state velocity is unchanged. -/
theorem power_scale_gauge (A : E →L[ℝ] E) (B : E →L[ℝ] F) (s : ℝ) (g : E) :
    ⟪(Real.exp s) ^ (2 : ℕ) • g,
      generator ((Real.exp (-s)) ^ (2 : ℕ) • A) (Real.exp (-s) • B)
        ((Real.exp s) ^ (2 : ℕ) • g)⟫_ℝ =
      (Real.exp s) ^ (2 : ℕ) * ⟪g, generator A B g⟫_ℝ := by
  rw [force_scale_gauge, real_inner_smul_left]

/-- A continuum of positive scales has the same velocity but a different potential calibration. -/
theorem scale_gauge_positive (s : ℝ) : 0 < (Real.exp s) ^ (2 : ℕ) :=
  sq_pos_of_pos (Real.exp_pos s)

end
end GaloisForLFunctions.HTGeometry.SchafferExl
