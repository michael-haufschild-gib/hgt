import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Small commutative-algebra identities used by literal horizon jets. -/

namespace GaloisForLFunctions.HTGeometry

theorem horizonPowerThird_algebra (x y z p : ℂ) :
    (z + 2 * x * y) * p + (y + x ^ (2 : ℕ)) * (x * p) =
      (z + 3 * y * x + x ^ (3 : ℕ)) * p := by
  ring

end GaloisForLFunctions.HTGeometry
