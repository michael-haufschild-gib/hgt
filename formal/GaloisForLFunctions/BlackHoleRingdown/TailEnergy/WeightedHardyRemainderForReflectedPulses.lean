import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.RegularityAndReceiverEquivalence
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Weighted Hardy identity for reflected pulses

In the logarithmic coordinate of a modular return, the ground-state transform
of the weighted Hardy inequality of Yang, Gu, Zhao and Zhou, Lemma 2.5
(arXiv:2611.22698), gives a finite-window identity. The endpoint fluxes
measure exactly what is lost when the receiver has no Dirichlet boundary.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Reflected energy on an oriented interval, with exponential time weight. -/
def weightedReceiverEnergy (h : CompactPulse) (s a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.exp (2*s*t)*‖pulseReflected h t‖^2

/-- The density left after conjugating the derivative by the exponential weight. -/
def hardyRemainder (h : CompactPulse) (s t : ℝ) : ℝ :=
  Real.exp (2*s*t)*‖s • pulseReflected h t + pulseReflected h.D t‖^2

private lemma continuous_hardyRemainder (h : CompactPulse) (s : ℝ) :
    Continuous (hardyRemainder h s) := by
  have he : Continuous (fun t : ℝ => Real.exp (2*s*t)) :=
    Real.continuous_exp.comp (continuous_id.const_mul (2*s))
  have hd : Continuous (fun t : ℝ => s • pulseReflected h t + pulseReflected h.D t) :=
    ((continuous_pulseReflected h).const_smul s).add (continuous_pulseReflected h.D)
  exact he.mul (hd.norm.pow 2)

private lemma boundary_derivative (h : CompactPulse) (s t : ℝ) :
    HasDerivAt (fun u => s * (Real.exp (2*s*u)*‖pulseReflected h u‖^2))
      (hardyRemainder h s t + s^2*(Real.exp (2*s*t)*‖pulseReflected h t‖^2) -
        Real.exp (2*s*t)*‖pulseReflected h.D t‖^2) t := by
  have he := (((hasDerivAt_id t).const_mul (2*s)).exp)
  have hn := (hasDerivAt_pulseReflected h t).norm_sq
  refine ((he.mul hn).const_mul s).congr_deriv ?_
  dsimp only [id_eq, hardyRemainder]
  rw [norm_add_sq_real, real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The square of the shifted derivative gives the exact Hardy remainder.
The formula also holds for reversed windows and zero weight. -/
theorem weightedReceiver_hardy_identity (h : CompactPulse) (s a b : ℝ) :
    (∫ t in a..b, hardyRemainder h s t) + s^2*weightedReceiverEnergy h s a b =
      weightedReceiverEnergy h.D s a b +
        s*(Real.exp (2*s*b)*‖pulseReflected h b‖^2 -
          Real.exp (2*s*a)*‖pulseReflected h a‖^2) := by
  have hc (g : CompactPulse) : Continuous (fun t => Real.exp (2*s*t)*‖pulseReflected g t‖^2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_pulseReflected g).norm.pow 2)
  have h₁ := (continuous_hardyRemainder h s).intervalIntegrable a b (μ := volume)
  have h₂ := ((hc h).const_mul (s^2)).intervalIntegrable a b (μ := volume)
  have h₃ := (hc h.D).intervalIntegrable a b (μ := volume)
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => boundary_derivative h s t) ((h₁.add h₂).sub h₃)
  rw [intervalIntegral.integral_sub (h₁.add h₂) h₃, intervalIntegral.integral_add h₁ h₂,
    intervalIntegral.integral_const_mul] at hft
  unfold weightedReceiverEnergy
  linarith only [hft]

/-- On a forward window the final receiver trace pays for any shortfall
of the derivative energy, with the initial trace appearing on the opposite side. -/
theorem weightedReceiver_hardy_bound (h : CompactPulse) (s : ℝ) {a b : ℝ} (hab : a ≤ b) :
    s^2*weightedReceiverEnergy h s a b + s*Real.exp (2*s*a)*‖pulseReflected h a‖^2 ≤
      weightedReceiverEnergy h.D s a b + s*Real.exp (2*s*b)*‖pulseReflected h b‖^2 := by
  have hn : 0 ≤ ∫ t in a..b, hardyRemainder h s t :=
    intervalIntegral.integral_nonneg hab fun t _ =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  linarith only [weightedReceiver_hardy_identity h s a b, hn]

#print axioms weightedReceiver_hardy_identity
#print axioms weightedReceiver_hardy_bound

end GaloisForLFunctions.BlackHoleRingdown
