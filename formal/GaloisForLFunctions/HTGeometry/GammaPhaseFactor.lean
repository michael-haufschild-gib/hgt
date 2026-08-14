import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Gamma phase factor of the frequency transport

The scalar half of the frequency propagator is

`p_L(η) = exp (i η L + (i/2) ∫₀^η r)`,

a unimodular factor whose logarithmic derivative is exactly the shifted symbol `i (L + r(η)/2)`.
Together with the bounded operator factor `exp (-i η T/2)` this is the transport `W_L` of the
high-frequency estimate: the whole Gamma phase is carried, none of it discarded.
-/

open Complex intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The scalar Gamma phase at frequency `L`, with `Rint` a primitive of the symbol. -/
def gammaPhase (L : ℝ) (Rint : ℝ → ℝ) (η : ℝ) : ℂ :=
  Complex.exp (((η * L + Rint η / 2 : ℝ)) * I)

theorem norm_gammaPhase (L : ℝ) (Rint : ℝ → ℝ) (η : ℝ) : ‖gammaPhase L Rint η‖ = 1 := by
  rw [gammaPhase, Complex.norm_exp]
  simp

/-- **The logarithmic derivative of the phase is the shifted symbol.** -/
theorem hasDerivAt_gammaPhase {Rint r : ℝ → ℝ} {L η : ℝ}
    (hRint : HasDerivAt Rint (r η) η) :
    HasDerivAt (gammaPhase L Rint)
      ((((L + r η / 2 : ℝ)) * I) * gammaPhase L Rint η) η := by
  have hlin : HasDerivAt (fun x : ℝ => (x * L + Rint x / 2 : ℝ)) (L + r η / 2) η := by
    have h1 : HasDerivAt (fun x : ℝ => x * L) L η := by
      simpa using (hasDerivAt_id' η).mul_const L
    have h2 : HasDerivAt (fun x : ℝ => Rint x / 2) (r η / 2) η := hRint.div_const 2
    exact h1.add h2
  have hcast : HasDerivAt (fun x : ℝ => (((x * L + Rint x / 2 : ℝ)) : ℂ))
      (((L + r η / 2 : ℝ)) : ℂ) η := hlin.ofReal_comp
  have hmul : HasDerivAt (fun x : ℝ => (((x * L + Rint x / 2 : ℝ)) : ℂ) * I)
      ((((L + r η / 2 : ℝ)) : ℂ) * I) η := hcast.mul_const I
  have hexp := hmul.cexp
  have hval : Complex.exp ((((η * L + Rint η / 2 : ℝ)) : ℂ) * I)
      * ((((L + r η / 2 : ℝ)) : ℂ) * I)
      = ((((L + r η / 2 : ℝ)) : ℂ) * I) * gammaPhase L Rint η := by
    rw [gammaPhase]
    ring
  have hgoal : HasDerivAt (gammaPhase L Rint)
      (Complex.exp ((((η * L + Rint η / 2 : ℝ)) : ℂ) * I) * ((((L + r η / 2 : ℝ)) : ℂ) * I)) η :=
    hexp
  rw [hval] at hgoal
  exact hgoal

/-- The phase is inverted by the shifted symbol: this is the identity that one integration by parts
uses on the high-frequency ray. -/
theorem gammaPhase_eq_inv_mul_deriv {Rint r : ℝ → ℝ} {L η : ℝ} (hL : 0 < L)
    (hr : 0 ≤ r η) :
    gammaPhase L Rint η
      = (((L + r η / 2 : ℝ)) : ℂ)⁻¹ * ((((L + r η / 2 : ℝ)) : ℂ) * gammaPhase L Rint η) := by
  have hpos : (0:ℝ) < L + r η / 2 := by linarith
  have hne : (((L + r η / 2 : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The shifted symbol dominates the frequency: `‖(L + r/2)⁻¹‖ ≤ 1/L`. -/
theorem norm_inv_shifted_symbol_le {r : ℝ → ℝ} {L η : ℝ} (hL : 0 < L) (hr : 0 ≤ r η) :
    ‖(((L + r η / 2 : ℝ)) : ℂ)⁻¹‖ ≤ 1 / L := by
  have hpos : (0:ℝ) < L + r η / 2 := by linarith
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, one_div]
  exact inv_anti₀ hL (by linarith)

end

end GaloisForLFunctions.HTGeometry
