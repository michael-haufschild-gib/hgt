import GaloisForLFunctions.Bottcher.SeibergWittenTopologicalShadow
import GaloisForLFunctions.HTGeometry.SeibergWittenFlatGaugeFlow

/-!
# Böttcher winding together with a flat Seiberg--Witten Dirac flow

The Böttcher module already isolates a product-system relation: one quadratic step doubles a
far-field Wilson winding while a finite spinor-curvature invariant is retained.  The flat
Seiberg--Witten layer adds a genuine chiral Dirac statement: the spatially constant phase orbit
lies in the kernel of the constructed Dirac operator.

The conjunction below records these two exact, independent facts.  It does not identify Böttcher
dynamics with a solution of a Seiberg--Witten curvature equation.
-/

noncomputable section

open Topology unitInterval

namespace Bottcher

open GaloisForLFunctions.HTGeometry
open LoopGaugeApplications

/-- Along the flat phase orbit, the chiral Dirac equation holds while a Böttcher quadratic step
doubles the independent Wilson-winding coordinate. -/
theorem flatDiracBottcherQuadraticFlow
    (t : ℝ) (psi : SeibergWittenSpinor) (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀) :
    SeibergWitten.flatChiralDiracEquation
      (flatSeibergWittenGaugeFlow.actOnSpinor t (flatConstantSpinorSection psi)) ∧
    (seibergWittenInvariant psi,
      wind (fun x : escapeOpen c => quadratic c (x : ℂ))
        ((continuous_quadratic c).comp continuous_subtype_val)
        (fun x => by
          have hx : quadratic c (x : ℂ) ∈ escapeOpen c := by
            have h := escapeOpen_iterate (c := c) (z := (x : ℂ)) x.2 1
            simpa [Function.iterate_one] using h
          exact escapeOpen_coe_ne_zero c ⟨quadratic c (x : ℂ), hx⟩) p) =
      (seibergWittenInvariant psi, 2 * farFieldWilsonWinding c p) := by
  exact ⟨flatSeibergWittenGaugeFlow_solves_flatChiralDiracEquation t psi,
    seibergWittenBottcherQuadraticFlow psi c p⟩

end Bottcher
