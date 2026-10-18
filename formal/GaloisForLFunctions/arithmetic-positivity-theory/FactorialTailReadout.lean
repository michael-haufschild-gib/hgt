import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailFourierEnergy
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzAnalyticRepair
import Zeta23.WeilEF.VerticalLine

/-! Exact Mellin/Fourier normalization and the actual half-plane of holomorphy.
The analytic domain follows from the corrected-minus-compact source identity. -/

open MeasureTheory Set
open _root_.Zeta23 _root_.RHTower
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The literal Mellin readout of the factorial correction tail. -/
def factorialTailReadout (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)

private theorem paperFT_gamma_readout (f : ℝ → ℝ) (s : ℂ) :
    paperFT (fun x => (f x : ℂ)) (gammaOf s) =
      ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(f x : ℂ) := by
  simp only [paperFT,gammaOf,mul_div_cancel₀ _ Complex.I_ne_zero,mul_comm]

theorem factorialTailReadout_eq_paperFT (n : ℕ) (s : ℂ) :
    factorialTailReadout n s =
      paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) (gammaOf s) :=
  (paperFT_gamma_readout (factorialMuntzCorrectedTail n) s).symm

/-- The raw readout is holomorphic on its admitted half-plane. -/
theorem factorialTailReadout_analyticOnNhd (n : ℕ) :
    AnalyticOnNhd ℂ (factorialTailReadout n) {s : ℂ | -1 < s.re} := by
  let r : ℝ → ℝ := sourceFactorialRamp (n+1)
  have hrc : Continuous (fun x : ℝ => (r x : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_sourceFactorialRamp (n+1))
  have hrcs : HasCompactSupport (fun x : ℝ => (r x : ℂ)) :=
    (hasCompactSupport_sourceFactorialRamp (N := n+1) (by omega)).comp_left Complex.ofReal_zero
  have hr : Differentiable ℂ (fun s : ℂ =>
      ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(r x : ℂ)) := by
    have h := (WeilEF.differentiable_paperFT hrc hrcs).comp
      (show Differentiable ℂ gammaOf by unfold gammaOf; fun_prop)
    simpa only [Function.comp_def,paperFT_gamma_readout] using h
  have hd : DifferentiableOn ℂ (fun s : ℂ =>
      (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
        (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))-
      (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(r x : ℂ))) {s : ℂ | -1 < s.re} := by
    intro s hs
    exact ((factorialMuntzBoundaryCorrected_readout_differentiableAt n hs).sub
      (hr s)).differentiableWithinAt
  have he : DifferentiableOn ℂ (factorialTailReadout n) {s : ℂ | -1 < s.re} :=
    hd.congr (fun s hs => (factorialMuntzBoundaryCorrected_readout_sub_ramp n s hs).symm)
  exact he.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- The Fourier convention fixes the imaginary coordinate with its exact sign and scale. -/
theorem factorialTailReadout_fourier (n : ℕ) (σ ξ : ℝ) :
    factorialTailReadout n ((σ : ℂ)-((2*Real.pi*ξ : ℝ) : ℂ)*Complex.I) =
      factorialTailFourier n σ ξ := by
  rw [factorialTailFourier,fourier_eq_paperFT_neg_two_pi_mul]
  unfold factorialTailReadout paperFT
  apply integral_congr_ae
  filter_upwards [] with x
  have he : (((σ : ℂ)-((2*Real.pi*ξ : ℝ) : ℂ)*Complex.I)-1/2)*(x : ℂ) =
      (((σ-1/2)*x : ℝ) : ℂ)+Complex.I*((-(2*Real.pi*ξ) : ℝ) : ℂ)*(x : ℂ) := by
    push_cast
    ring
  rw [he,Complex.exp_add]
  simp only [factorialWeightedTail,Complex.ofReal_mul,Complex.ofReal_exp]
  ring

/-- Vertical Mellin lines use the reflected Fourier coordinate `-t/(2*pi)`. -/
theorem factorialTailReadout_add_im_eq_fourier (n : ℕ) (σ t : ℝ) :
    factorialTailReadout n ((σ : ℂ)+(t : ℂ)*Complex.I) =
      factorialTailFourier n σ (-t/(2*Real.pi)) := by
  have ht : 2*Real.pi*(-t/(2*Real.pi)) = -t := by
    field_simp
  have hs : (σ : ℂ)+(t : ℂ)*Complex.I =
      (σ : ℂ)-((2*Real.pi*(-t/(2*Real.pi)) : ℝ) : ℂ)*Complex.I := by
    rw [ht,Complex.ofReal_neg]
    ring
  rw [hs,factorialTailReadout_fourier]

end
end GaloisForLFunctions.ArithmeticPositivityTheory
