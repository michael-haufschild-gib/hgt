import GaloisForLFunctions.Bottcher.BoundaryArcCovering
import Mathlib.Analysis.Calculus.ImplicitContDiff

open Complex Metric Set Filter Topology
open scoped ContDiff

namespace Bottcher

/-- **Relation ⟹ boundary continuation (the interior half of the answer-05 supplier).** If `h` on the
unit disk satisfies a holomorphic relation `f (z, h z) = 0` near a boundary point `ζ`, has a boundary
limit `h → w₀` at `ζ` (the sole Fatou-type input, taken as a hypothesis), and `(ζ, w₀)` is a **simple**
root of the relation (the `∂_w`-derivative is invertible), then `h` continues holomorphically across
`ζ`.  The continuation is the holomorphic implicit-function branch `ψ` of `f (·, ·) = 0` through
`(ζ, w₀)`; the implicit function is `C^∞` over `ℂ` (hence holomorphic on a neighborhood of `ζ`), and its
local uniqueness pins `ψ = h` on the inner side. -/
theorem continuesAcross_of_relation {h : ℂ → ℂ} {ζ w₀ : ℂ}
    (f : ℂ × ℂ → ℂ)
    (hf : ContDiffAt ℂ ⊤ f (ζ, w₀))
    (hroot : f (ζ, w₀) = 0)
    (hsimple : (fderiv ℂ f (ζ, w₀) ∘L .inr ℂ ℂ ℂ).IsInvertible)
    (hrel : ∀ᶠ z in 𝓝[ball 0 1] ζ, f (z, h z) = 0)
    (hlim : Tendsto h (𝓝[ball 0 1] ζ) (𝓝 w₀)) :
    ContinuesAcross h ζ := by
  have pn : (⊤ : ℕ∞ω) ≠ 0 := by simp
  set ψ := ContDiffAt.implicitFunction hf pn hsimple with hψdef
  have hψcd : ContDiffAt ℂ ⊤ ψ ζ := ContDiffAt.contDiffAt_implicitFunction hf pn hsimple
  -- ψ is holomorphic on a neighbourhood of ζ
  obtain ⟨U₀, hU₀nhds, hU₀diff⟩ : ∃ U ∈ 𝓝 ζ, DifferentiableOn ℂ ψ U := by
    obtain ⟨U, hU, hcd⟩ :=
      ContDiffAt.contDiffOn hψcd (m := 1) (by exact_mod_cast le_top) (fun _ => rfl)
    exact ⟨U, hU, hcd.differentiableOn (by norm_num)⟩
  -- the graph map tends to (ζ, w₀) along the inner side
  have htend : Tendsto (fun z => (z, h z)) (𝓝[ball 0 1] ζ) (𝓝 (ζ, w₀)) := by
    rw [nhds_prod_eq]
    exact Tendsto.prodMk (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) hlim
  have hiff := ContDiffAt.eventually_apply_eq_iff_implicitFunction hf pn hsimple
  -- uniqueness pins ψ = h on the inner side
  have hmatch : ∀ᶠ z in 𝓝[ball 0 1] ζ, ψ z = h z := by
    filter_upwards [htend.eventually hiff, hrel] with z hz hzrel
    have hfeq : f (z, h z) = f (ζ, w₀) := by rw [hzrel, hroot]
    exact hz.mp hfeq
  -- extract an open ball realising both the differentiability and the matching
  obtain ⟨δ, hδ, hballU⟩ := Metric.mem_nhds_iff.mp hU₀nhds
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hmatch
  obtain ⟨ε, hε, hmatch'⟩ := hmatch
  refine ⟨ball ζ (min δ ε), isOpen_ball, mem_ball_self (lt_min hδ hε), ψ, ?_, ?_⟩
  · exact hU₀diff.mono ((ball_subset_ball (min_le_left _ _)).trans hballU)
  · intro z hz
    obtain ⟨hzball, hz1⟩ := hz
    have hzε : dist z ζ < ε := lt_of_lt_of_le (mem_ball.mp hzball) (min_le_right _ _)
    exact hmatch' hzε hz1

/-- **Abstract transcendence obstruction (answer-05/06 skeleton).** For `c ∉ {0, -2}`, an even
Böttcher-FE solution `h` on the disk (`h 0 = 1`) cannot satisfy — at every point of a boundary arc — a
holomorphic relation with a simple root and a boundary limit. If it did, `continuesAcross_of_relation`
would continue `h` across the whole arc, contradicting the natural boundary `natural_boundary_of_even_fe`.
The two boundary-limit hypotheses `Tendsto h … (𝓝 w₀)` are exactly the Fatou-type input (absent from
mathlib) that the full connected-transcendence supplier must produce; here it is made explicit. -/
theorem cmem_of_arc_relation {h : ℂ → ℂ} {c : ℂ} {ζ₀ : ℂ} {r : ℝ}
    (hζ₀ : ‖ζ₀‖ = 1) (hr : 0 < r)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ z ∈ ball (0 : ℂ) 1, h (-z) = h z)
    (hfe : ∀ t ∈ ball (0 : ℂ) 1, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (hh0 : h 0 = 1)
    (hrelarc : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ∈ ball ζ₀ r →
      ∃ (f : ℂ × ℂ → ℂ) (w₀ : ℂ), ContDiffAt ℂ ⊤ f (ζ, w₀) ∧ f (ζ, w₀) = 0 ∧
        (fderiv ℂ f (ζ, w₀) ∘L .inr ℂ ℂ ℂ).IsInvertible ∧
        (∀ᶠ z in 𝓝[ball 0 1] ζ, f (z, h z) = 0) ∧ Tendsto h (𝓝[ball 0 1] ζ) (𝓝 w₀)) :
    c = 0 ∨ c = -2 := by
  by_contra hcon
  push Not at hcon
  refine natural_boundary_of_even_fe hcon.1 hcon.2 hζ₀ hr hhd hhe hfe hh0 ?_
  intro ζ hζ1 hζr
  obtain ⟨f, w₀, hf, hroot, hsimple, hrel, hlim⟩ := hrelarc ζ hζ1 hζr
  exact continuesAcross_of_relation f hf hroot hsimple hrel hlim

end Bottcher
