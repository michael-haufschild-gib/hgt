import GaloisForLFunctions.BiScaleUncertainty.FactorialCompleteFormCoercivity
import GaloisForLFunctions.BiScaleUncertainty.CompactFiniteJumpWeilFormula

/-! Unconditional logarithmic coercivity of the literal spectral Weil functional
on both reflected balanced factorial source families. -/

open MeasureTheory Set Filter
open scoped FourierTransform
open Zeta23
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

theorem factorialPacketSource_jump_integrable (n : ℕ) (b : Bool) :
    IntegrableOn (fun x => (autocorr (factorialPacketSource n b) 0-
      autocorr (factorialPacketSource n b) x)*archLevySinhWeight x) (Ioi 0) := by
  simp only [factorialPacketSource_autocorr]
  cases b
  · exact factorialSourcePlus_jump_integrable n
  · exact factorialSourceMinus_jump_integrable n

/-- Spectral integrability is derived from the concrete source, without a
smoothness or spectral-domain premise. -/
theorem factorialPacketSource_spectral_integrable (n : ℕ) (b : Bool) :
    Integrable (fun ξ : ℝ => gammaHardyPhaseRate (2*Real.pi*ξ)*
      ‖𝓕 (fun u => (factorialPacketSource n b u : ℂ)) ξ‖^2) :=
  integrable_archSymbol_of_compact_finite_jump (factorialPacketSource n b)
    (factorialPacketSource_jump_integrable n b)

theorem factorialPacketSource_weil_eq_complete (n : ℕ) (b : Bool) :
    (weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
      (EF.weilTest (fun u => (factorialPacketSource n b u : ℂ))
        (fun u => (factorialPacketSource n b u : ℂ)))).re = factorialCompleteEnergy n b :=
  re_weilFullFunctional_eq_of_compact_finite_jump (factorialPacketSource n b)
    (factorialPacketSource_jump_integrable n b)

/-- The complete signed Weil form has a source-derived logarithmic lower bound. -/
theorem factorialPacketSource_weil_normalized_lower (n : ℕ) (b : Bool) :
    EF.gammaBracket 0+factorialSourceNormalizedJumpLower n-448 ≤
      (weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
        (EF.weilTest (fun u => (factorialPacketSource n b u : ℂ))
          (fun u => (factorialPacketSource n b u : ℂ)))).re /
            autocorr (factorialPacketSource n b) 0 := by
  rw [factorialPacketSource_weil_eq_complete]
  exact factorialCompleteEnergy_normalized_lower n b

theorem factorialPacketSource_weil_normalized_tendsto (b : Bool) :
    Tendsto (fun n =>
      (weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
        (EF.weilTest (fun u => (factorialPacketSource n b u : ℂ))
          (fun u => (factorialPacketSource n b u : ℂ)))).re /
            autocorr (factorialPacketSource n b) 0) atTop atTop := by
  simp only [factorialPacketSource_weil_eq_complete]
  exact factorialCompleteEnergy_normalized_tendsto b

/-- Both actual spectral Weil energies are eventually strictly positive. -/
theorem factorialPacketSource_weil_eventually_pos :
    ∀ᶠ n in atTop, ∀ b : Bool,
      0 < (weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
        (EF.weilTest (fun u => (factorialPacketSource n b u : ℂ))
          (fun u => (factorialPacketSource n b u : ℂ)))).re := by
  simp only [factorialPacketSource_weil_eq_complete]
  exact factorialCompleteEnergy_eventually_pos

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
