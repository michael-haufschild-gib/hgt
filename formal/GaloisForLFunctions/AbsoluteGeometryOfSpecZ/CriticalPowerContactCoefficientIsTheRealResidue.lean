import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerCombConvergencePaysHarmonicContacts
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanMellinIntegral
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorSymbolSplitsAtTheZeros
import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingHankel
import GaloisForLFunctions.RHTower.SiegelRealAxis
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# The critical harmonic coefficient equals the real contact residue

The functional equation makes the completed logarithmic derivative vanish
at one half. The archimedean row is twice the Gamma logarithmic derivative,
so the harmonic coefficient removed from the critical contacts is exactly
the real residue of their Dirichlet symbol.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The analytic factor multiplying the critical zeta pole. -/
def criticalPowerContactFactor (s : ℂ) : ℂ :=
  -deriv riemannZeta (s + 1 / 2) / riemannZeta (s + 1 / 2) -
    riemannZeta (s + 1 / 2)

/-- Harmonic subtraction removes precisely the real pole; its coefficient
is fixed by the functional equation rather than a convergence premise. -/
theorem criticalPowerContactCoefficient_eq_realResidue :
    (criticalPowerContactCoefficient : ℂ) = criticalPowerContactFactor 0 := by
  have hζ : riemannZeta (1 / 2) ≠ 0 := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
      _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hreal : ((riemannZeta ((1 / 2 : ℝ) : ℂ)).re : ℂ) = riemannZeta (1 / 2) := by
    have hi := _root_.RHTower.riemannZeta_ofReal_im (1 / 2)
    norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hi ⊢
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using hi.symm
  have hxi := ArithmeticCorrespondencePositivity.logDeriv_xi_eq_add
    (by norm_num : 0 < (1 / 2 : ℂ).re) (by norm_num : (1 / 2 : ℂ) ≠ 1) hζ
  have hpoles : ∀ n : ℕ, (1 / 2 : ℂ) / 2 ≠ -(n : ℂ) := by
    intro n he
    have hh := congrArg Complex.re he
    norm_num at hh
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [hh, hn]
  rw [_root_.RHTower.logDeriv_xi_one_half, BohrGeneratorAxis.logDeriv_GammaR _ hpoles,
    logDeriv_apply] at hxi
  norm_num at hxi
  have harch := ofReal_powerTailArchimedeanRowLimit
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at harch
  norm_num at harch
  rw [criticalPowerContactCoefficient, ofReal_sub, ofReal_div, ofReal_ofNat, hreal,
    harch, criticalPowerContactFactor, zero_add]
  linear_combination -hxi

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
