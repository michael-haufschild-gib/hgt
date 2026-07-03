/-
# Transport: the unit-circle reflection formula landed on `ContinuesAcross`

`schwarzReflect_unit_circle` (`SchwarzReflectionUnitFormula.lean`) reflects across the *unit* circle.
The smooth Julia arc `{‖φ‖ = 1}` becomes the unit circle after composing with the local inverse
`γ = φ⁻¹` of the branch `φ`.  This file transports the reflection: with `F = β ∘ γ`, the reflected
extension pulled back by `φ`,

  `f = reflectUnit (β ∘ γ) ∘ φ`,

is analytic at the frontier arc point `z₀` (composition of the analytic `reflectUnit (β∘γ)` at
`φ z₀` with the analytic `φ` at `z₀`), and agrees with `β` on the basin side (there `‖φ‖ > 1`, so
`reflectUnit (β∘γ)(φ z) = β(γ(φ z)) = β z`).  Hence `β` continues analytically across `z₀`.

This lands the full reflection route on the natural-boundary target: `continuesAcross_of_reflected_boundary`
produces a `ContinuesAcross β (filledJulia c₁)ᶜ z₀` witness, which contradicts the proven natural
boundary `hnb`.  The remaining inputs are exactly the boundary datum of `F = β ∘ γ` at the arc
(continuity up to the circle + modulus one — the boundary regularity of the exterior Böttcher map at
the smooth piece) and the local-inverse / basin-side geometry, all supplied as explicit hypotheses.
The analytic continuation itself — the reflection — is fully discharged here.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import GaloisForLFunctions.Bottcher.Q62ReflectionBridge
import GaloisForLFunctions.Bottcher.SchwarzReflectionUnitFormula

open Complex Set Filter Topology

namespace Bottcher

/-- **The reflection route, transported and landed on `ContinuesAcross`.**  At a frontier arc point
`z₀` where the branch `φ` is a local biholomorphism (analytic, `deriv φ z₀ ≠ 0`, `‖φ z₀‖ = 1`, local
inverse `γ`), given the boundary datum of `F = β ∘ γ` on the unit circle around `w₀ = φ z₀`
(holomorphic outside, continuous up to the circle, nonzero outside, modulus one on the circle) and
that the basin side maps to the outer side (`‖φ‖ > 1` on `𝓝[K₁ᶜ] z₀`), the Böttcher branch `β`
continues analytically across `z₀`.  The continuation is `reflectUnit (β ∘ γ) ∘ φ`. -/
theorem continuesAcross_of_reflected_boundary
    {c₁ : ℂ} {β φ γ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hφAt : AnalyticAt ℂ φ z₀) (hmod : ‖φ z₀‖ = 1)
    (hγφ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, γ (φ z) = z)
    (hFcont : ContinuousOn (β ∘ γ) ({v | 1 ≤ ‖v‖} ∩ Metric.ball (φ z₀) r))
    (hFhol : DifferentiableOn ℂ (β ∘ γ) ({v | 1 < ‖v‖} ∩ Metric.ball (φ z₀) r))
    (hFne : ∀ v ∈ {v : ℂ | 1 ≤ ‖v‖} ∩ Metric.ball (φ z₀) r, (β ∘ γ) v ≠ 0)
    (hFmod : ∀ v ∈ {v : ℂ | ‖v‖ = 1} ∩ Metric.ball (φ z₀) r, ‖(β ∘ γ) v‖ = 1)
    (hbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  -- reflected extension in `w`-space, analytic at `w₀ = φ z₀`
  have hAn : AnalyticAt ℂ (reflectUnit (β ∘ γ)) (φ z₀) :=
    schwarzReflect_unit_circle hr hmod hFcont hFhol hFne hFmod
  -- pull back by `φ`: analytic at `z₀`
  have hfAn : AnalyticAt ℂ (fun z => reflectUnit (β ∘ γ) (φ z)) z₀ := hAn.comp hφAt
  -- agrees with `β` on the basin side
  have hagree : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, reflectUnit (β ∘ γ) (φ z) = β z := by
    filter_upwards [hbasin, hγφ] with z hz1 hz2
    rw [reflectUnit, if_pos (le_of_lt hz1)]
    simp only [Function.comp_apply]
    rw [hz2]
  exact ⟨fun z => reflectUnit (β ∘ γ) (φ z), hfAn, hagree⟩

end Bottcher
