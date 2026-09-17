import GaloisForLFunctions.HTGeometry.HorizonAffinePowerJetCore

/-!
Exact jets of the source power multiplied by its retained affine radial bracket.

The literal source remainder is a fixed amplitude times this expression, with
`α = 2s - w` and its two displayed angular coefficients substituted for `B₀`
and `B₁`. This re-exports the checked derivative algebra with the source-facing
names used by the three-counterterm continuation.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Literal source power times the retained degree-one radial source bracket. -/
abbrev literalSourceAffinePower := horizonAffinePowerCore

abbrev literalSourceAffinePowerFirst := horizonAffinePowerCoreFirst

abbrev literalSourceAffinePowerSecond := horizonAffinePowerCoreSecond

/-- The affine source factor has its literal first and second radial derivatives. -/
theorem literalSourceAffinePower_derivatives (α B₀ B₁ : ℂ) {z : ℝ} (hz : z < 1) :
    HasDerivAt (literalSourceAffinePower α B₀ B₁)
      (literalSourceAffinePowerFirst α B₀ B₁ z) z ∧
      HasDerivAt (literalSourceAffinePowerFirst α B₀ B₁)
        (literalSourceAffinePowerSecond α B₀ B₁ z) z :=
  horizonAffinePowerCore_derivatives α B₀ B₁ hz

/-- The exact degree-zero through degree-two coefficients of the literal affine
source factor. The final equality gives the Taylor coefficient, not the raw
second derivative. -/
theorem literalSourceAffinePower_zero_jets (α B₀ B₁ : ℂ) :
    literalSourceAffinePower α B₀ B₁ 0 = literalSourceHorizonPower α 0 * B₀ ∧
      literalSourceAffinePowerFirst α B₀ B₁ 0 =
        literalSourceHorizonPower α 0 * (-(α * B₀ / 4) - B₁) ∧
        literalSourceAffinePowerSecond α B₀ B₁ 0 / 2 = literalSourceHorizonPower α 0 *
          (α * (α - 3) * B₀ / 32 + α * B₁ / 4) :=
  horizonAffinePowerCore_zero_jets α B₀ B₁

end
end GaloisForLFunctions.HTGeometry
