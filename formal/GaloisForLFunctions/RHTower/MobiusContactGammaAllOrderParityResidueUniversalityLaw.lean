import GaloisForLFunctions.HTGeometry.GammaFactorialAllOrderZetaLayer
import GaloisForLFunctions.HTGeometry.GammaFactorialTailCovariantResidueUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma all-order parity residue universality

The finite Möbius contact defect is the arithmetic coordinate of the complete proved polygamma
parity hierarchy. Odd orders expose nonzero zeta residues. The adjacent even orders cancel at the
leading correction, and their first magnified finite tails recover intrinsic covariant residues.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Möbius-contact presentation of the all-order Gamma factorial microscope scale. -/
def mobiusContactGammaParityFactorialScale (n : ℕ) : ℂ :=
  (-2 - mobiusGammaContactPartialCharge n) / 2

theorem mobiusContactGammaParityFactorialScale_eq (n : ℕ) :
    mobiusContactGammaParityFactorialScale n =
      GaloisForLFunctions.reciprocalGammaFactorialScale n := by
  rw [mobiusContactGammaParityFactorialScale, mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

/-- **Möbius-contact Gamma all-order parity residue universality law.** The same finite contact
coordinate exposes nonzero zeta residues at every odd order and cancellation followed by the
adjacent covariant-residue norm at every positive even order. -/
theorem mobiusContactGammaAllOrder_completeParityResidueUniversality :
    ∀ r : ℕ, ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n : ℕ =>
        (GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 1) n x -
            ((2 * r + 1).factorial : ℂ) / x ^ (2 * r + 2)) /
          mobiusContactGammaParityFactorialScale n ^ (2 * r + 2)) atTop
        (𝓝 (2 * (((2 * r + 1).factorial : ℂ) *
          riemannZeta ((2 * r + 2 : ℕ) : ℂ)))) ∧
      2 * (((2 * r + 1).factorial : ℂ) *
          riemannZeta ((2 * r + 2 : ℕ) : ℂ)) ≠ 0 ∧
      Tendsto (fun n : ℕ =>
        (GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 2) n x -
            (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
          mobiusContactGammaParityFactorialScale n ^ (2 * r + 3)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((((n + 1 : ℕ) : ℂ) ^ (2 * r + 2)) *
        ((GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 2) n x -
            (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
          mobiusContactGammaParityFactorialScale n ^ (2 * r + 3)))) atTop
        (𝓝 (-(‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue 0 (2 * r + 1)
          (Fin.last (2 * r + 1))‖ : ℂ))) := by
  intro r x hx
  exact ⟨by
      simpa only [mobiusContactGammaParityFactorialScale_eq] using
        (GaloisForLFunctions.tendsto_gammaFactorialScaledPolygamma_odd_correction r hx),
    GaloisForLFunctions.gammaFactorialScaledPolygamma_odd_correction_limit_ne_zero r,
    by
      simpa only [mobiusContactGammaParityFactorialScale_eq] using
        (GaloisForLFunctions.tendsto_gammaFactorialScaledPolygamma_even_correction r hx),
    by
      simpa only [mobiusContactGammaParityFactorialScale_eq] using
        (GaloisForLFunctions.tendsto_gammaFactorialScaledPolygamma_even_finiteTail_eq_neg_covariantResidueNorm
          r hx)⟩

end

end GaloisForLFunctions.RHTower
