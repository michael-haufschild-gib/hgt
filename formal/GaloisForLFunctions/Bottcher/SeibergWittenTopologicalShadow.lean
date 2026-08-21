import GaloisForLFunctions.Bottcher.LoopGaugeApplications
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Böttcher-flow topological shadow of a finite Seiberg--Witten invariant

The Böttcher corpus proves that a quadratic step doubles its Abelian Wilson winding.  This module
packages that independent topological charge together with the finite spinor-curvature invariant.
The result is a product-system law, not a claim that quadratic complex dynamics solves the
Seiberg--Witten PDE or defines a Seiberg--Witten curve.
-/

noncomputable section

open Topology unitInterval

namespace Bottcher

open GaloisForLFunctions.HTGeometry
open LoopGaugeApplications

/-- Joint spinor-curvature and far-field Wilson-winding record. -/
def seibergWittenBottcherTopologicalShadow (ψ : SeibergWittenSpinor)
    (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀) : SeibergWittenCurvature × ℤ :=
  (seibergWittenInvariant ψ, farFieldWilsonWinding c p)

/-- Common spinor phase leaves the Böttcher topological shadow unchanged. -/
theorem seibergWittenBottcherTopologicalShadow_gaugeInvariant
    (u : Circle) (ψ : SeibergWittenSpinor) (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀) :
    seibergWittenBottcherTopologicalShadow (u • ψ) c p =
      seibergWittenBottcherTopologicalShadow ψ c p := by
  unfold seibergWittenBottcherTopologicalShadow
  rw [seibergWittenInvariant_gaugeInvariant]

/-- Under one quadratic Böttcher flow step, the topological coordinate doubles while the
independent finite spinor-curvature invariant is unchanged. -/
theorem seibergWittenBottcherQuadraticFlow
    (ψ : SeibergWittenSpinor) (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀) :
    (seibergWittenInvariant ψ,
      wind (fun x : escapeOpen c => quadratic c (x : ℂ))
        ((continuous_quadratic c).comp continuous_subtype_val)
        (fun x => by
          have hx : quadratic c (x : ℂ) ∈ escapeOpen c := by
            have h := escapeOpen_iterate (c := c) (z := (x : ℂ)) x.2 1
            simpa [Function.iterate_one] using h
          exact escapeOpen_coe_ne_zero c ⟨quadratic c (x : ℂ), hx⟩) p) =
      (seibergWittenInvariant ψ, 2 * farFieldWilsonWinding c p) := by
  exact congrArg (fun n : ℤ => (seibergWittenInvariant ψ, n))
    (quadraticWilsonLoop_doubles c p)

end Bottcher
