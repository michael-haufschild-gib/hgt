import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFunctionCriterion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOriginLogarithmicRemainder

open Complex

noncomputable section

namespace RHTower

/-- The complex screw used by Suzuki's integral operator is the complexification of the real
source screw in the 2026 differential-operator paper. -/
theorem suzukiScrewG_eq_sourceScrew_core (t : ℝ) :
    suzukiScrewG t =
      (GaloisForLFunctions.RHTower.suzukiSourceScrew t : ℂ) := by
  have hreal : -suzukiPsi t =
      GaloisForLFunctions.RHTower.suzukiSourceScrew t := by
    rw [suzukiPsi, GaloisForLFunctions.RHTower.suzukiSourceScrew, neg_neg]
  calc
    suzukiScrewG t = -(suzukiPsi t : ℂ) := rfl
    _ = ((-suzukiPsi t : ℝ) : ℂ) := by rw [Complex.ofReal_neg]
    _ = (GaloisForLFunctions.RHTower.suzukiSourceScrew t : ℂ) :=
      congrArg Complex.ofReal hreal

end RHTower

end
