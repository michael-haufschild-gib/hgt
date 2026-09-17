import GaloisForLFunctions.HTGeometry.LiteralSourceHorizonPowerJets

/-! Internal derivative algebra for the literal affine source factor. -/

namespace GaloisForLFunctions.HTGeometry
open Complex
noncomputable section
set_option autoImplicit false

def horizonAffinePowerCore (α B₀ B₁ : ℂ) (z : ℝ) : ℂ :=
  literalSourceHorizonPower α z * (B₀ - (z : ℂ) * B₁)

def horizonAffinePowerCoreFirst (α B₀ B₁ : ℂ) (z : ℝ) : ℂ :=
  literalSourceHorizonPowerFirst α z * (B₀ - (z : ℂ) * B₁) -
    literalSourceHorizonPower α z * B₁

def horizonAffinePowerCoreSecond (α B₀ B₁ : ℂ) (z : ℝ) : ℂ :=
  literalSourceHorizonPowerSecond α z * (B₀ - (z : ℂ) * B₁) -
    2 * literalSourceHorizonPowerFirst α z * B₁

theorem horizonAffinePowerCore_derivatives (α B₀ B₁ : ℂ) {z : ℝ} (hz : z < 1) :
    HasDerivAt (horizonAffinePowerCore α B₀ B₁) (horizonAffinePowerCoreFirst α B₀ B₁ z) z ∧
      HasDerivAt (horizonAffinePowerCoreFirst α B₀ B₁)
        (horizonAffinePowerCoreSecond α B₀ B₁ z) z := by
  have hp := literalSourceHorizonPower_derivatives α hz
  have hq : HasDerivAt (fun x : ℝ => B₀ - (x : ℂ) * B₁) (-B₁) z := by
    have ht := (hasDerivAt_const z B₀).sub
      ((Complex.ofRealCLM.hasDerivAt (x := z)).mul_const B₁)
    change HasDerivAt ((fun _ : ℝ => B₀) - (fun x : ℝ => (x : ℂ) * B₁)) (-B₁) z
    simpa using ht
  constructor
  · have hprod := hp.1.mul hq
    apply hprod.congr_deriv
    dsimp [horizonAffinePowerCore, horizonAffinePowerCoreFirst]
    ring
  · have hleft := hp.2.mul hq
    have hright := hp.1.const_mul (-B₁)
    have hsum := hleft.add hright
    have he : horizonAffinePowerCoreFirst α B₀ B₁ =
        (literalSourceHorizonPowerFirst α * fun x : ℝ => B₀ - (x : ℂ) * B₁) +
          fun x : ℝ => -B₁ * literalSourceHorizonPower α x := by
      funext x
      dsimp [horizonAffinePowerCoreFirst]
      ring
    rw [he]
    apply hsum.congr_deriv
    dsimp [horizonAffinePowerCoreSecond]
    ring

theorem horizonAffinePowerCore_zero_jets (α B₀ B₁ : ℂ) :
    horizonAffinePowerCore α B₀ B₁ 0 = literalSourceHorizonPower α 0 * B₀ ∧
      horizonAffinePowerCoreFirst α B₀ B₁ 0 =
        literalSourceHorizonPower α 0 * (-(α * B₀ / 4) - B₁) ∧
        horizonAffinePowerCoreSecond α B₀ B₁ 0 / 2 = literalSourceHorizonPower α 0 *
          (α * (α - 3) * B₀ / 32 + α * B₁ / 4) := by
  have hp := literalSourceHorizonPower_zero_jets α
  constructor
  · simp [horizonAffinePowerCore]
  constructor
  · rw [horizonAffinePowerCoreFirst, hp.2.1]
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    ring
  · have hp2 : literalSourceHorizonPowerSecond α 0 =
      α * (α - 3) / 16 * literalSourceHorizonPower α 0 := by
      calc
        literalSourceHorizonPowerSecond α 0 =
            2 * (literalSourceHorizonPowerSecond α 0 / 2) := by ring
        _ = 2 * (α * (α - 3) / 32 * literalSourceHorizonPower α 0) := by rw [hp.2.2]
        _ = α * (α - 3) / 16 * literalSourceHorizonPower α 0 := by ring
    rw [horizonAffinePowerCoreSecond, hp.2.1, hp2]
    simp only [Complex.ofReal_zero, zero_mul, sub_zero]
    ring

end
end GaloisForLFunctions.HTGeometry
