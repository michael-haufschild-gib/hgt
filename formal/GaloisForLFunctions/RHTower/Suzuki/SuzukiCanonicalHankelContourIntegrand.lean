import GaloisForLFunctions.RHTower.MellinUniformBoundedStripAllOrder
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalShiftRatio

/-!
# Suzuki's exact logarithmic contour integrand

This lightweight leaf owns the common exact integrand used by the inner and finite-pole contour
transport arguments.
-/

namespace RHTower

open Complex

noncomputable section

/-- Exact contour integrand in Suzuki's logarithmic inverse-Mellin proof. -/
def suzukiCanonicalHankelContourIntegrand
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget)
    (r : ℝ) (z : ℂ) : ℂ :=
  suzukiCanonicalTheta omega z *
    deningerMeyerStrongLogMellin g (-Complex.I * z) *
    Complex.exp (-Complex.I * z * (r : ℂ))

end

end RHTower
