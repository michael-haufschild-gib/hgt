import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbePhaseDynamics
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeZeroPhaseSensitivity

/-!
# Exact return probabilities for zero-coordinate phase orbits

The orbit is a linear combination of a vector and its reflected partner.
A half-period is functional-equation reflection. The single-coordinate
return probability is constant on the critical line and follows the
two-level cosine law off it.
-/

noncomputable section
open scoped ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23

/-- The phase orbit stays in the span of a vector and its actual reflected partner. -/
theorem phaseRotate_reflection_expansion (u : Circle) (x : ZeroSpace) :
    phaseRotate u x = ((1 + (u : ℂ)) / 2) • x +
      ((1 - (u : ℂ)) / 2) • zeroReflection x := by
  unfold phaseRotate positivePart negativePart
  module

/-- Half a phase period is exactly functional-equation reflection. -/
theorem timePhase_pi (x : ZeroSpace) : timePhase Real.pi x = zeroReflection x := by
  rw [timePhase, phaseRotate_reflection_expansion, Circle.coe_exp, Complex.exp_pi_mul_I]
  norm_num

/-- A full phase period closes the orbit exactly. -/
theorem timePhase_two_pi (x : ZeroSpace) : timePhase (2 * Real.pi) x = x := by
  rw [two_mul, timePhase_add, timePhase_pi, timePhase_pi, zeroReflection_involutive]

private theorem phase_distance_sq (t : ℝ) :
    ‖(1 : ℂ) - (Circle.exp t : ℂ)‖ ^ 2 = 2 - 2 * Real.cos t := by
  have hre : (Circle.exp t : ℂ).re = Real.cos t := by
    rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp only [Circle.normSq_coe, map_one, one_mul,
    Complex.conj_re, hre]
  ring

/-- Exact probability of returning to the original zero coordinate at real time. -/
theorem zeroBasis_survival_probability (z : zetaZeroConfig.carrier) (t : ℝ) :
    ‖inner ℂ (zeroBasis z) (timePhase t (zeroBasis z))‖ ^ 2 =
      if (z : ℂ).re = 1 / 2 then 1 else (1 + Real.cos t) / 2 := by
  classical
  have h := zeroBasis_projective_loss z 1 (Circle.exp t)
  rw [phaseRotate_one, Circle.coe_one, phase_distance_sq] at h
  change 1 - ‖inner ℂ (zeroBasis z) (timePhase t (zeroBasis z))‖ ^ 2 = _ at h
  by_cases hz : (z : ℂ).re = 1 / 2
  · rw [if_pos hz] at h ⊢
    linarith only [h]
  · rw [if_neg hz] at h ⊢
    linarith only [h]

/-- A half-period returns to the original coordinate exactly on the critical line. -/
theorem zeroBasis_half_period_survival (z : zetaZeroConfig.carrier) :
    ‖inner ℂ (zeroBasis z) (zeroReflection (zeroBasis z))‖ ^ 2 =
      if (z : ℂ).re = 1 / 2 then 1 else 0 := by
  have h := zeroBasis_survival_probability z Real.pi
  simpa only [timePhase_pi, Real.cos_pi, add_neg_cancel, zero_div] using h

#print axioms phaseRotate_reflection_expansion
#print axioms timePhase_pi
#print axioms timePhase_two_pi
#print axioms zeroBasis_survival_probability
#print axioms zeroBasis_half_period_survival
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
