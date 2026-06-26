/-
# Böttcher tower — Brolin / Riesz-measure interface

This file names the missing potential-theoretic object for the quadratic Green
function.  Mathlib has distributional Laplacians and the Riesz-Markov theorem,
but it does not yet provide the planar Riesz decomposition theorem for
subharmonic functions, so the existence theorem for `μ_c` is kept as a compact
checked interface:

* `IsRieszMeasureOf μ u` says `μ = (2π)⁻¹ Δu` in distributional form.
* `HasGreenPotentialRepresentation c μ` says `G_c = -U^μ`, equivalently
  `G_c = greenFunction μ 0`.
* `BrolinMeasure c` packages the probability/support/Riesz/potential data.

Everything here is definition/projection code only; the remaining work is the
actual Riesz-decomposition existence proof producing a `BrolinMeasure c`.
-/
import GaloisForLFunctions.Bottcher.Capacity
import GaloisForLFunctions.Bottcher.GreenContinuity
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

/-- Distributional Riesz-measure condition.

`IsRieszMeasureOf μ u` means `μ = (2π)⁻¹ Δu`: testing against a compactly
supported continuous function `φ`, the measure integral is the distributional
Laplacian action of `u` on `φ`.
-/
def IsRieszMeasureOf (μ : Measure ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    ∫ z, φ z ∂μ = (2 * Real.pi)⁻¹ * ∫ z, u z * (Δ (φ : ℂ → ℝ)) z

/-- The positive functional whose Riesz-Markov measure is `(2π)⁻¹Δu`. -/
def IsRieszFunctional (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) (u : ℂ → ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Λ φ = (2 * Real.pi)⁻¹ * ∫ z, u z * (Δ (φ : ℂ → ℝ)) z

/-- The Riesz-Markov measure represented by a positive compact-support functional. -/
noncomputable def rieszMeasureOfFunctional (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) : Measure ℂ :=
  RealRMK.rieszMeasure Λ

/-- If a positive functional is the distributional Laplacian of `u`, its
Riesz-Markov measure is the Riesz measure of `u`. -/
theorem isRieszMeasureOf_rieszMeasureOfFunctional
    {Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ} {u : ℂ → ℝ}
    (hΛ : IsRieszFunctional Λ u) :
    IsRieszMeasureOf (rieszMeasureOfFunctional Λ) u := by
  intro φ
  rw [rieszMeasureOfFunctional, RealRMK.integral_rieszMeasure, hΛ φ]

/-- A Riesz measure for `u`, constructed as a genuine Riesz-Markov measure of a
positive compact-support functional. -/
structure RieszMeasure (u : ℂ → ℝ) where
  functional : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ
  isFunctional : IsRieszFunctional functional u

namespace RieszMeasure

/-- The underlying Riesz-Markov measure. -/
noncomputable def measure (R : RieszMeasure u) : Measure ℂ :=
  rieszMeasureOfFunctional R.functional

theorem isRieszMeasure (R : RieszMeasure u) :
    IsRieszMeasureOf R.measure u :=
  isRieszMeasureOf_rieszMeasureOfFunctional R.isFunctional

end RieszMeasure

/-- The dynamical Green function is represented by the logarithmic potential of
`μ` with Robin constant zero: `G_c(z) = -U^μ(z)`.

For monic quadratic polynomials the Robin constant is zero (`cap K_c = 1`), so
this is the potential representation used in the Brolin step.
-/
def HasGreenPotentialRepresentation (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ z : ℂ, greenFunctionDyn c z = greenFunction μ 0 z

/-- Expanded form of the zero-Robin potential representation. -/
theorem hasGreenPotentialRepresentation_iff (c : ℂ) (μ : Measure ℂ) :
    HasGreenPotentialRepresentation c μ ↔
      ∀ z : ℂ, greenFunctionDyn c z = - logPotential μ z := by
  constructor
  · intro h z
    simpa [HasGreenPotentialRepresentation, greenFunction] using h z
  · intro h z
    simpa [HasGreenPotentialRepresentation, greenFunction] using h z

/-- `μ` is the Brolin/Riesz measure of the quadratic Green function `G_c`. -/
def IsBrolinMeasure (c : ℂ) (μ : Measure ℂ) : Prop :=
  IsProbOn μ (filledJulia c) ∧
    IsRieszMeasureOf μ (greenFunctionDyn c) ∧
    HasGreenPotentialRepresentation c μ

/-- A packaged Brolin measure for `f_c(z)=z²+c`. -/
structure BrolinMeasure (c : ℂ) where
  riesz : RieszMeasure (greenFunctionDyn c)
  isProbOn : IsProbOn riesz.measure (filledJulia c)
  potential : HasGreenPotentialRepresentation c riesz.measure

namespace BrolinMeasure

/-- The underlying measure, named for downstream code as `μ_c`. -/
noncomputable def μ (M : BrolinMeasure c) : Measure ℂ := M.riesz.measure

theorem isBrolinMeasure (M : BrolinMeasure c) : IsBrolinMeasure c M.μ :=
  ⟨M.isProbOn, M.riesz.isRieszMeasure, M.potential⟩

theorem probOn (M : BrolinMeasure c) : IsProbOn M.μ (filledJulia c) :=
  M.isProbOn

theorem isRieszMeasure (M : BrolinMeasure c) :
    IsRieszMeasureOf M.μ (greenFunctionDyn c) :=
  M.riesz.isRieszMeasure

/-- **Potential representation.** The packaged Brolin measure satisfies
`G_c(z) = -U^{μ_c}(z)`. -/
theorem potentialRepresentation (M : BrolinMeasure c) (z : ℂ) :
    greenFunctionDyn c z = - logPotential M.μ z :=
  (hasGreenPotentialRepresentation_iff c M.μ).mp M.potential z

/-- Equivalent Green-function notation for the same potential representation. -/
theorem greenFunctionRepresentation (M : BrolinMeasure c) (z : ℂ) :
    greenFunctionDyn c z = greenFunction M.μ 0 z :=
  M.potential z

end BrolinMeasure

/-- Direct projection from the predicate form. -/
theorem potentialRepresentation_of_isBrolinMeasure {c : ℂ} {μ : Measure ℂ}
    (hμ : IsBrolinMeasure c μ) (z : ℂ) :
    greenFunctionDyn c z = - logPotential μ z :=
  (hasGreenPotentialRepresentation_iff c μ).mp hμ.2.2 z

/-- Direct projection of the Riesz condition from the predicate form. -/
theorem isRieszMeasureOf_greenFunctionDyn_of_isBrolinMeasure {c : ℂ} {μ : Measure ℂ}
    (hμ : IsBrolinMeasure c μ) :
    IsRieszMeasureOf μ (greenFunctionDyn c) :=
  hμ.2.1

end Bottcher
