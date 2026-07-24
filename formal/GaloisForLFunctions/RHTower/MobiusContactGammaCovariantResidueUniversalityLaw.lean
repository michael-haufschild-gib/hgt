import GaloisForLFunctions.HTGeometry.GammaFactorialTailCovariantResidueUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius contact charge as the Gamma covariant-residue scale

The displacement of the raw finite Möbius--Gamma contact charge from its terminal value is exactly
twice Gamma's reciprocal factorial pole scale.  Substitution into the all-order finite-tail theorem
makes this arithmetic boundary-charge defect the normalization of every even Gamma
covariant-residue limit.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Half the oriented displacement from the raw Möbius contact charge to its terminal charge
`-2` is exactly Gamma's signed reciprocal factorial pole scale. -/
theorem mobiusGammaContactPartialCharge_defect_eq_reciprocalGammaFactorialScale
    (N : ℕ) :
    (-2 - mobiusGammaContactPartialCharge N) / 2 =
      GaloisForLFunctions.reciprocalGammaFactorialScale N := by
  rw [mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

/-- **Möbius-contact/Gamma covariant-residue universality law.**  At every even microscope order,
the raw Möbius contact-charge defect supplies the exact normalization whose Gamma factorial tail
converges to the negative norm of the adjacent intrinsic covariant residue. -/
theorem
    tendsto_gammaFactorialScaledPolygamma_even_finiteTail_normalizedBy_mobiusContactDefect
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => ((((n + 1 : ℕ) : ℂ) ^ (2 * r + 2)) *
      ((GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 2) n x -
          (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
        ((-2 - mobiusGammaContactPartialCharge n) / 2) ^ (2 * r + 3)))) atTop
      (𝓝 (-(‖GaloisForLFunctions.gammaPoleCovariantTopResidueValue
        0 (2 * r + 1) (Fin.last (2 * r + 1))‖ : ℂ))) := by
  simpa only [
    mobiusGammaContactPartialCharge_defect_eq_reciprocalGammaFactorialScale] using
    (GaloisForLFunctions.tendsto_gammaFactorialScaledPolygamma_even_finiteTail_eq_neg_covariantResidueNorm
      r hx)

end

end GaloisForLFunctions.RHTower
