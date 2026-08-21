import GaloisForLFunctions.Bottcher.BottcherWinding

/-!
# Loop-gauge applications in Böttcher dynamics

Premise-free abelian Wilson-winding consequences on the far-field escape region.  Quadratic
dynamics acts on loop charge by degree two, and the Böttcher coordinate retains that charge.
-/

noncomputable section

open Topology unitInterval

namespace Bottcher.LoopGaugeApplications

/-- Abelian Wilson winding of a far-field loop around the puncture. -/
def farFieldWilsonWinding (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀) : ℤ :=
  wind (fun x : escapeOpen c => (x : ℂ)) continuous_subtype_val
    (fun x => escapeOpen_coe_ne_zero c x) p

/-- One quadratic evolution doubles the abelian Wilson winding. -/
theorem quadraticWilsonLoop_doubles (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀) :
    wind (fun x : escapeOpen c => quadratic c (x : ℂ))
        ((continuous_quadratic c).comp continuous_subtype_val)
        (fun x => by
          have hx : quadratic c (x : ℂ) ∈ escapeOpen c := by
            have h := escapeOpen_iterate (c := c) (z := (x : ℂ)) x.2 1
            simpa [Function.iterate_one] using h
          exact escapeOpen_coe_ne_zero c ⟨quadratic c (x : ℂ), hx⟩) p
      = 2 * farFieldWilsonWinding c p :=
  wind_quadratic_escapeOpen c p

/-- After `n` quadratic evolutions, Wilson winding is multiplied by the exact degree `2^n`. -/
theorem iteratedQuadraticWilsonLoop_degree (c : ℂ) (n : ℕ)
    {x₀ : escapeOpen c} (p : Path x₀ x₀) :
    wind (fun x : escapeOpen c => (quadratic c)^[n] (x : ℂ))
        (((continuous_quadratic c).iterate n).comp continuous_subtype_val)
        (fun x => escapeOpen_coe_ne_zero c
          ⟨(quadratic c)^[n] (x : ℂ), escapeOpen_iterate x.2 n⟩) p
      = (2 : ℤ) ^ n * farFieldWilsonWinding c p :=
  wind_quadratic_iterate_escapeOpen c n p

/-- The Böttcher-coordinate loop has the same `2^n` Wilson degree as the position loop. -/
theorem bottcherWilsonLoop_degree (c : ℂ) (n : ℕ)
    {x₀ : escapeOpen c} (p : Path x₀ x₀) :
    wind (fun x : escapeOpen c => bottcherCoord c ((quadratic c)^[n] (x : ℂ)))
        (continuous_bottcherCoord_iterate_escapeOpen c n)
        (fun _ => bottcherCoord_ne_zero c _) p
      = (2 : ℤ) ^ n * farFieldWilsonWinding c p :=
  wind_bottcherCoord_iterate_escapeOpen c n p

end Bottcher.LoopGaugeApplications
