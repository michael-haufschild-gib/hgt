import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateIntegrability
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear critical Tate functionals and the radial spanning law

Absolute convergence upgrades the ramified critical Mellin integrals to
complex-linear functionals on the full p-adic Bruhat space.  Their functional
equation defect is therefore a linear functional.  This file proves that the
defect vanishes on the entire finite linear span of inverse-character radial
packets, not merely on individual packets.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

variable (p : ℕ) [Fact p.Prime]

def fieldOnePadicCriticalTateLinear (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle) :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ] ℂ where
  toFun f := ∫ a, fieldOnePadicCriticalTateIntegrand p n χ ρ f a
    ∂fieldOnePadicMultiplicativeHaar p
  map_add' f g := by
    have hf := integrable_fieldOnePadicCriticalTateIntegrand p n χ ρ f
    have hg := integrable_fieldOnePadicCriticalTateIntegrand p n χ ρ g
    have hpoint : (fun a =>
        fieldOnePadicCriticalTateIntegrand p n χ ρ
          (fun x => f.1 x + g.1 x) a) =
        fun a => fieldOnePadicCriticalTateIntegrand p n χ ρ f a +
          fieldOnePadicCriticalTateIntegrand p n χ ρ g a := by
      funext a
      unfold fieldOnePadicCriticalTateIntegrand
      change (f.1 (a : ℚ_[p]) + g.1 (a : ℚ_[p])) * _ * _ = _
      ring
    change (∫ a, fieldOnePadicCriticalTateIntegrand p n χ ρ
        (fun x => f.1 x + g.1 x) a
      ∂fieldOnePadicMultiplicativeHaar p) = _
    rw [hpoint, integral_add hf hg]
  map_smul' c f := by
    have hf := integrable_fieldOnePadicCriticalTateIntegrand p n χ ρ f
    have hpoint : (fun a =>
        fieldOnePadicCriticalTateIntegrand p n χ ρ (c • f) a) =
        fun a => c * fieldOnePadicCriticalTateIntegrand p n χ ρ f a := by
      funext a
      unfold fieldOnePadicCriticalTateIntegrand
      change (c * f.1 (a : ℚ_[p])) * _ * _ = _
      ring
    change (∫ a, fieldOnePadicCriticalTateIntegrand p n χ ρ (c • f) a
      ∂fieldOnePadicMultiplicativeHaar p) = c *
        ∫ a, fieldOnePadicCriticalTateIntegrand p n χ ρ f a
          ∂fieldOnePadicMultiplicativeHaar p
    rw [hpoint, integral_const_mul]

def fieldOnePadicDualCriticalTateLinear (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle) :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ] ℂ where
  toFun f := ∫ a, fieldOnePadicDualCriticalTateIntegrand p n χ ρ f a
    ∂fieldOnePadicMultiplicativeHaar p
  map_add' f g := by
    have hf := integrable_fieldOnePadicDualCriticalTateIntegrand p n χ ρ f
    have hg := integrable_fieldOnePadicDualCriticalTateIntegrand p n χ ρ g
    have hpoint : (fun a =>
        fieldOnePadicDualCriticalTateIntegrand p n χ ρ
          (fun x => f.1 x + g.1 x) a) =
        fun a => fieldOnePadicDualCriticalTateIntegrand p n χ ρ f a +
          fieldOnePadicDualCriticalTateIntegrand p n χ ρ g a := by
      funext a
      unfold fieldOnePadicDualCriticalTateIntegrand
      change (f.1 (a : ℚ_[p]) + g.1 (a : ℚ_[p])) * _ * _ = _
      ring
    change (∫ a, fieldOnePadicDualCriticalTateIntegrand p n χ ρ
        (fun x => f.1 x + g.1 x) a
      ∂fieldOnePadicMultiplicativeHaar p) = _
    rw [hpoint, integral_add hf hg]
  map_smul' c f := by
    have hf := integrable_fieldOnePadicDualCriticalTateIntegrand p n χ ρ f
    have hpoint : (fun a =>
        fieldOnePadicDualCriticalTateIntegrand p n χ ρ (c • f) a) =
        fun a => c * fieldOnePadicDualCriticalTateIntegrand p n χ ρ f a := by
      funext a
      unfold fieldOnePadicDualCriticalTateIntegrand
      change (c * f.1 (a : ℚ_[p])) * _ * _ = _
      ring
    change (∫ a, fieldOnePadicDualCriticalTateIntegrand p n χ ρ (c • f) a
      ∂fieldOnePadicMultiplicativeHaar p) = c *
        ∫ a, fieldOnePadicDualCriticalTateIntegrand p n χ ρ f a
          ∂fieldOnePadicMultiplicativeHaar p
    rw [hpoint, integral_const_mul]

def fieldOnePadicRamifiedTateDefectLinear (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle) :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ] ℂ :=
  (fieldOnePadicDualCriticalTateLinear p n χ ρ).comp
      (fieldOnePadicBruhatFourierLinear p) -
    (fieldOnePadicRamifiedTatePhase p n χ ρ) •
      fieldOnePadicCriticalTateLinear p n χ ρ

def fieldOnePadicPrimitiveRadialPacketInvSynthesis (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    (ℤ →₀ ℂ) →ₗ[ℂ] compactlySupportedLocallyConstant ℚ_[p] :=
  Finsupp.linearCombination ℂ (fun m =>
    fieldOnePadicPrimitiveRadialPacket p n
      (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m)

theorem fieldOnePadicRamifiedTateDefectLinear_radialPacket
    (n : ℕ+) (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ))
    (ρ : Circle) (m : ℤ) :
    fieldOnePadicRamifiedTateDefectLinear p (n : ℕ) χ ρ
      (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
        (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m) = 0 := by
  unfold fieldOnePadicRamifiedTateDefectLinear
  change
    (∫ a, fieldOnePadicDualCriticalTateIntegrand p (n : ℕ) χ ρ
        (fieldOnePadicBruhatFourierBruhat p
          (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
            (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m)) a
        ∂fieldOnePadicMultiplicativeHaar p) -
      fieldOnePadicRamifiedTatePhase p (n : ℕ) χ ρ *
        (∫ a, fieldOnePadicCriticalTateIntegrand p (n : ℕ) χ ρ
          (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
            (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m) a
          ∂fieldOnePadicMultiplicativeHaar p) = 0
  rw [show fieldOnePadicDualCriticalTateIntegrand p (n : ℕ) χ ρ
      (fieldOnePadicBruhatFourierBruhat p
        (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
          (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m)) =
      fieldOnePadicDualCriticalTateIntegrand p (n : ℕ) χ ρ
        (fieldOnePadicBruhatFourier p
          (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
            (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m)) by rfl]
  rw [fieldOnePadicDualCriticalTateIntegral_fourier_radialPacketInv
      p (n : ℕ) n.pos χ ρ m,
    fieldOnePadicCriticalTateIntegral_radialPacketInv
      p (n : ℕ) n.pos χ ρ m,
    fieldOnePadicRamifiedFourierShellConstant_eq_phase_mul]
  ring

theorem fieldOnePadicRamifiedTateDefectLinear_synthesis
    (n : ℕ+) (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ))
    (ρ : Circle) (c : ℤ →₀ ℂ) :
    fieldOnePadicRamifiedTateDefectLinear p (n : ℕ) χ ρ
      (fieldOnePadicPrimitiveRadialPacketInvSynthesis p (n : ℕ) χ c) = 0 := by
  rw [fieldOnePadicPrimitiveRadialPacketInvSynthesis,
    Finsupp.linearCombination_apply, Finsupp.sum]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [map_smul,
    fieldOnePadicRamifiedTateDefectLinear_radialPacket p n χ ρ m,
    smul_zero]

end
end GaloisForLFunctions.RHTower
