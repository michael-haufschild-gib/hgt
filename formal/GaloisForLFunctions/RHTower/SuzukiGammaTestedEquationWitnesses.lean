import GaloisForLFunctions.RHTower.SuzukiGammaMollifiedEquation

/-!
# Unconditional tested-equation witnesses

The tested Suzuki-Gamma equation is a genuine weak integro-differential equation, not a property
of arbitrary profiles.  Its zero profile supplies the unconditional consistency witness.
-/

namespace GaloisForLFunctions.RHTower

/-- The zero source and zero response satisfy the tested equation for every parameter pair. -/
theorem suzukiGammaTestedEquation_zero (σ τ : ℝ) :
    SuzukiGammaTestedEquation σ τ (fun _ => 0) (fun _ => 0) := by
  intro φ hφ hsupp
  simp

end GaloisForLFunctions.RHTower
