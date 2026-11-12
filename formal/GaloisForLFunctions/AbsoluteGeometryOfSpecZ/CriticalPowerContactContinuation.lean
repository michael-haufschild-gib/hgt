import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactDirichletSymbol
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ContactSymbolsContinueAcrossZeros

/-!
# Critical contact continuation from harmonic centering

The centered transform is holomorphic on the right half-plane. Clearing
zeta's poles continues its actual Dirichlet symbol throughout that domain.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Convergence of the critical comb forces the actual contact symbol to
agree with its holomorphic centered transform throughout `Re s>0`. -/
theorem criticalPowerContactMellin_eq
    (hc : PowerCombTailConverges (1 / 2)) {s : ℂ} (hs : 0 < s.re)
    (hs1 : s + (1 / 2 : ℝ) ≠ 1) (hζ : riemannZeta (s + (1 / 2 : ℝ)) ≠ 0) :
    criticalPowerContactMellin s =
      riemannZeta (s + 1) *
        (-deriv riemannZeta (s + (1 / 2 : ℝ)) / riemannZeta (s + (1 / 2 : ℝ)) -
          riemannZeta (s + (1 / 2 : ℝ))) := by
  have hF : DifferentiableOn ℂ criticalPowerContactMellin
      {z : ℂ | 1 - 2 * (1 / 2 : ℝ) < z.re} := by
    simpa only [show 1 - 2 * (1 / 2 : ℝ) = 0 by ring] using
      differentiableOn_criticalPowerContactMellin hc
  have hi : ∀ z : ℂ, 2 < z.re → criticalPowerContactMellin z =
      riemannZeta (z + ((2 * (1 / 2 : ℝ) : ℝ) : ℂ)) *
        (-deriv riemannZeta (z + (1 / 2 : ℝ)) / riemannZeta (z + (1 / 2 : ℝ)) -
          riemannZeta (z + (1 / 2 : ℝ))) := by
    intro z hz
    simpa only [show 2 * (1 / 2 : ℝ) = 1 by ring, ofReal_one] using
      criticalPowerContactMellin_initial hc hz
  have hh := contactSymbol_eq_of_holomorphic (by norm_num : (0 : ℝ) < 1 / 2) hF hi
    (show 1 - 2 * (1 / 2 : ℝ) < s.re by linarith only [hs]) hs1 hζ
  simpa only [show 2 * (1 / 2 : ℝ) = 1 by ring, ofReal_one] using hh

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
