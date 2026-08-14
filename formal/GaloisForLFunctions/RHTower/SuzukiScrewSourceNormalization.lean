import GaloisForLFunctions.RHTower.SuzukiEquationTwoFive
import GaloisForLFunctions.RHTower.SuzukiZeroMeanScrewCompression

/-!
# Equality of Suzuki's divisor and source screw normalizations

The zero-divisor construction and the arithmetic expansion historically introduced two names for
the same screw function.  This module closes that seam before either normalization is used in an
operator factorization.
-/

open Complex

noncomputable section

namespace RHTower

/-- The complex screw kernel used by `G_a` is exactly the real source screw occurring in Suzuki's
equations (2.2) and (2.5), with no sign, reflection, or scaling discrepancy. -/
theorem suzukiScrewG_eq_sourceScrew (t : ℝ) :
    suzukiScrewG t =
      (GaloisForLFunctions.RHTower.suzukiSourceScrew t : ℂ) := by
  simp [suzukiScrewG, suzukiPsi,
    GaloisForLFunctions.RHTower.suzukiSourceScrew]

end RHTower

end
