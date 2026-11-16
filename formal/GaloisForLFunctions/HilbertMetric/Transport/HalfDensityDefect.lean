import GaloisForLFunctions.RHTower.WeightOneFlowIsometry
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Transport, phase rotation, and the half-density coefficient

For amplitude transport with divergence coefficient c, the continuity
defect of the squared norm is (1-2c) times divergence times density.
The phase term cancels exactly. Thus c=1/2 is the unique coefficient
valid for every compressible flow. Arbitrary phase twists also preserve
the existing weighted half-density isometry.
-/

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

open MeasureTheory
open scoped ComplexConjugate

private theorem real_inner_complex (z w : ℂ) : inner ℝ z w = (w * conj z).re := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  rfl

/-- Local amplitude velocity: advection, divergence weight, and real phase rotation. -/
def amplitudeTransportRate (c d v ω : ℝ) (z gradient : ℂ) : ℂ :=
  -(v : ℂ) * gradient - (c * d : ℝ) * z + Complex.I * (ω : ℂ) * z

/-- Density derivative plus divergence of its flux. -/
def amplitudeContinuityDefect (c d v ω : ℝ) (z gradient : ℂ) : ℝ :=
  2 * inner ℝ z (amplitudeTransportRate c d v ω z gradient) +
    d * ‖z‖ ^ 2 + 2 * v * inner ℝ z gradient

/-- The imaginary phase cancels, leaving the exact compressibility defect. -/
theorem amplitudeContinuityDefect_eq (c d v ω : ℝ) (z gradient : ℂ) :
    amplitudeContinuityDefect c d v ω z gradient = (1 - 2 * c) * d * ‖z‖ ^ 2 := by
  unfold amplitudeContinuityDefect amplitudeTransportRate
  simp only [real_inner_complex, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Pointwise conservation holds precisely at half-density, zero divergence, or zero amplitude. -/
theorem amplitudeContinuityDefect_eq_zero_iff (c d v ω : ℝ) (z gradient : ℂ) :
    amplitudeContinuityDefect c d v ω z gradient = 0 ↔
      c = 1 / 2 ∨ d = 0 ∨ z = 0 := by
  rw [amplitudeContinuityDefect_eq, mul_eq_zero, mul_eq_zero]
  have hc : 1 - 2 * c = 0 ↔ c = 1 / 2 := by constructor <;> intro h <;> linarith
  simp only [hc, sq_eq_zero_iff, norm_eq_zero]
  tauto

/-- Universal density conservation uniquely determines the half-density coefficient. -/
theorem amplitudeTransport_conservative_iff (c : ℝ) :
    (∀ d v ω : ℝ, ∀ z gradient : ℂ,
      amplitudeContinuityDefect c d v ω z gradient = 0) ↔ c = 1 / 2 := by
  constructor
  · intro h
    have h₁ := h 1 0 0 1 0
    rw [amplitudeContinuityDefect_eq] at h₁
    norm_num at h₁
    linarith
  · rintro rfl d v ω z gradient
    rw [amplitudeContinuityDefect_eq]
    ring

/-- The algebraic identity is the actual continuity equation for differentiable fields. -/
theorem amplitudeTransport_continuityEquation
    (ψ : ℝ → ℝ → ℂ) (v : ℝ → ℝ) (t x c ω d : ℝ) (dt dx : ℂ)
    (ht : HasDerivAt (fun s => ψ s x) dt t)
    (hx : HasDerivAt (ψ t) dx x) (hv : HasDerivAt v d x)
    (heq : dt = amplitudeTransportRate c d (v x) ω (ψ t x) dx) :
    deriv (fun s => ‖ψ s x‖ ^ 2) t + deriv (fun y => v y * ‖ψ t y‖ ^ 2) x =
      (1 - 2 * c) * d * ‖ψ t x‖ ^ 2 := by
  change deriv (fun s => ‖ψ s x‖ ^ 2) t + deriv (v * fun y => ‖ψ t y‖ ^ 2) x = _
  rw [ht.norm_sq.deriv, (hv.mul hx.norm_sq).deriv, heq]
  have h := amplitudeContinuityDefect_eq c d (v x) ω (ψ t x) dx
  unfold amplitudeContinuityDefect at h
  linear_combination h

/-- An arbitrary real spatial phase has modulus one. -/
theorem norm_phaseTwist (θ : ℝ) (z : ℂ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) * z‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp

/-- Arbitrary phase twists preserve the actual weight-one centered-flow isometry. -/
theorem integral_exp_mul_normSq_phaseTwistedFlow
    (g : ℝ → ℂ) (c : ℝ) (θ : ℝ → ℝ) :
    (∫ t, Real.exp t * ‖Complex.exp (Complex.I * (θ t : ℂ)) *
        ((Real.exp (-c / 2) : ℂ) * g (t - c))‖ ^ 2) =
      ∫ t, Real.exp t * ‖g t‖ ^ 2 := by
  simp_rw [norm_phaseTwist]
  exact RHTower.integral_exp_mul_normSq_centeredFlow g c

/-- Pointwise weighted transport also forces the amplitude exponent to be one half. -/
theorem weightedAmplitude_exponent_iff (a : ℝ) :
    (∀ c t : ℝ, Real.exp t * Real.exp (-a * c) ^ 2 = Real.exp (t - c)) ↔
      a = 1 / 2 := by
  constructor
  · intro h
    have he := h 1 0
    rw [← Real.exp_nat_mul, ← Real.exp_add] at he
    have hlog := congrArg Real.log he
    simp only [Real.log_exp] at hlog
    norm_num at hlog
    linarith
  · rintro rfl c t
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring

#print axioms amplitudeContinuityDefect_eq_zero_iff
#print axioms amplitudeTransport_conservative_iff
#print axioms amplitudeTransport_continuityEquation
#print axioms integral_exp_mul_normSq_phaseTwistedFlow
#print axioms weightedAmplitude_exponent_iff

end GaloisForLFunctions.HilbertMetric
