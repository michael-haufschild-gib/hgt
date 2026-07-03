/-
# Natural boundary of the Böttcher branch for ALL connected `c ∈ mandelbrot ∖ {0,-2}`

The crux input of the both-connected q62 rigidity engine
(`RelativeRigidityNaturalBoundary.noRelation_phiMero_of_naturalBoundary_...`) is

  `hnb : ∀ z₀ ∈ frontier (filledJulia c), ¬ ContinuesAcross β (filledJulia c)ᶜ z₀`,

the statement that the global Böttcher branch `β` has the Julia frontier as a genuine natural boundary.
It was previously proven only for **empty-interior** connected `c` (dendrite / Misiurewicz /
`∂M`-type), via `hnb_of_emptyInterior_modulus`. The **interior-nonempty** case (hyperbolic components /
main cardioid, where `K_c` is a quasidisk) was the open sub-gap of #118.

This file closes it — for *every* connected `c ∈ mandelbrot ∖ {0,-2}`, with no interior hypothesis and
no quasidisk topology. The argument (all in `InteriorModulusObstruction`):

* a continuation `g` of `β` across a frontier point is, at a point where `deriv g ≠ 0`, a local
  biholomorphism, so the exterior level set `{|g|>1}` is the biholomorphic image of the connected
  exterior lune — hence connected — and lands wholly in the basin (`FrontierSeparation`, for free);
* the local inverse `γ` then agrees with the global inverse `ψ` on the whole exterior side
  (identity theorem on the lune), so the even-FE disk model `h` continues across the boundary point
  `t₀ = 1/(g z₀)` and, since the continuation domain is open, across a whole boundary arc —
  contradicting `natural_boundary_of_even_fe` (`c ∉ {0,-2}`);
* the `deriv g ≡ 0` edge makes `g` constant, so `‖g‖ ≡ 1` on an open set, killed directly.

`false_of_continuation_connected_package` packages the reduction on the connected Böttcher + even-FE
disk-model data; here that package is instantiated unconditionally from
`exists_full_disk_model_of_mem_mandelbrot` (with the branch modulus transferred from
`exists_global_branch_with_inverse_of_mem_mandelbrot` by the identity theorem), giving the fully
unconditional `hnb_of_mem_mandelbrot_connected`.

Axiom-clean.  This closes the `hnb` half of the both-connected pair; the exposure clause (#124) and the
`hinput` frontier-fibre producer remain the other inputs of `noRelation_phiMero_of_naturalBoundary_...`.
-/
import GaloisForLFunctions.Bottcher.InteriorModulusObstruction
import GaloisForLFunctions.Bottcher.DiskModelGlobal

open Complex Metric Set Topology Filter

namespace Bottcher

/-- **The crux `hnb` at one frontier point, on the connected Böttcher package.** For `c ∉ {0,-2}`
with a connected filled Julia set, the global Böttcher branch `β` (carrying the modulus, with global
inverse `ψ` analytic on the exterior and the even-FE disk model `h`) does NOT continue analytically
across a frontier point `z₀`. Adapts the abstract `U0NaturalBoundary.ContinuesAcross` predicate to the
explicit continuation data `(g, Ω)` — `AnalyticAt g z₀` gives analyticity on a ball, and the
`𝓝[basin]`-agreement gives `g = β` on the basin part of that ball — and closes it with
`false_of_continuation_connected_package`. No interior-nonempty hypothesis, no quasidisk topology. -/
theorem not_continuesAcross_beta_of_connected_package
    {c z₀ : ℂ} {β ψ h : ℂ → ℂ}
    (hc0 : c ≠ 0) (hc2 : c ≠ -2)
    (hconn : IsPreconnected (filledJulia c))
    (hz₀front : z₀ ∈ frontier (filledJulia c))
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψan : AnalyticOnNhd ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ t ∈ ball (0:ℂ) 1, h (-t) = h t)
    (hfe : ∀ t ∈ ball (0:ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2)
    (hh0 : h 0 = 1)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    ¬ U0NaturalBoundary.ContinuesAcross β (filledJulia c)ᶜ z₀ := by
  rintro ⟨g, hgAt, hgβev⟩
  obtain ⟨δ₁, hδ₁, hb1⟩ := Metric.eventually_nhds_iff.mp hgAt.eventually_analyticAt
  have hgβnhd : ∀ᶠ w in 𝓝 z₀, w ∈ (filledJulia c)ᶜ → g w = β w :=
    (eventually_nhdsWithin_iff).mp hgβev
  obtain ⟨δ₂, hδ₂, hb2⟩ := Metric.eventually_nhds_iff.mp hgβnhd
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁ hδ₂
  have hgAnΩ : AnalyticOnNhd ℂ g (Metric.ball z₀ δ) := fun w hw =>
    hb1 (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
  have hgβΩ : ∀ z ∈ Metric.ball z₀ δ ∩ (filledJulia c)ᶜ, g z = β z := by
    rintro z ⟨hzΩ, hzc⟩
    exact hb2 (lt_of_lt_of_le (Metric.mem_ball.mp hzΩ) (min_le_right _ _)) hzc
  exact false_of_continuation_connected_package hc0 hc2 hconn isOpen_ball
    (convex_ball z₀ δ).isPreconnected (Metric.mem_ball_self hδpos) hz₀front hgAnΩ hgβΩ
    hβmod hψan hψβ hhd hhe hfe hh0 hbridge

/-- **Natural boundary of the Böttcher branch, ALL connected `c ∈ mandelbrot ∖ {0,-2}` (uncondit.).**
For every connected `c ∈ mandelbrot ∖ {0,-2}` there is a global Böttcher branch `β` — analytic on the
basin, matching `bottcherCoord` on `escapeOpen`, carrying the modulus — whose Julia frontier is a
genuine natural boundary: `∀ z₀ ∈ frontier, ¬ ContinuesAcross β (filledJulia c)ᶜ z₀`. This is the crux
input `hnb` of the both-connected q62 rigidity engine, now proven with **no** empty-interior
hypothesis — closing the interior-nonempty (hyperbolic / quasidisk) sub-gap of #118. The branch, its
inverse `ψ`, and the even-FE disk model `h` are instantiated from
`exists_full_disk_model_of_mem_mandelbrot`; the branch modulus `hβmod` is transferred from
`exists_global_branch_with_inverse_of_mem_mandelbrot` by the identity theorem (both branches equal
`bottcherCoord` on the nonempty open `escapeOpen`, and the basin is preconnected); each frontier point
is discharged by `not_continuesAcross_beta_of_connected_package`. -/
theorem hnb_of_mem_mandelbrot_connected {c : ℂ}
    (hcM : c ∈ mandelbrot) (hc0 : c ≠ 0) (hc2 : c ≠ -2)
    (hconn : IsPreconnected (filledJulia c)) :
    ∃ β : ℂ → ℂ,
      AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z₀ ∈ frontier (filledJulia c),
        ¬ U0NaturalBoundary.ContinuesAcross β (filledJulia c)ᶜ z₀) := by
  obtain ⟨h, β, ψ, hhd, hhe, hfe, hh0, hbridge, hβan, hβesc, hψan, hψmem, hβψ, hψβ⟩ :=
    exists_full_disk_model_of_mem_mandelbrot c hcM
  obtain ⟨β₁, ψ₁, hβ₁an, hβ₁esc, hβ₁mod, hβ₁gt, hβ₁iter, hψ₁an, hψ₁mem, hβψ₁, hψβ₁⟩ :=
    exists_global_branch_with_inverse_of_mem_mandelbrot c hcM
  have hesc_ne : (escapeOpen c).Nonempty := ⟨_, deepPoint_mem_escapeOpen c⟩
  obtain ⟨zstar, hzstar⟩ := hesc_ne
  have hzstarbasin : zstar ∈ (filledJulia c)ᶜ := escapeOpen_subset_compl_filledJulia c hzstar
  have hev : β =ᶠ[𝓝 zstar] β₁ := by
    filter_upwards [(isOpen_escapeOpen c).mem_nhds hzstar] with z hz
    rw [hβesc z hz, hβ₁esc z hz]
  have hββ₁ : Set.EqOn β β₁ (filledJulia c)ᶜ :=
    hβan.eqOn_of_preconnected_of_eventuallyEq hβ₁an (isPreconnected_compl_filledJulia c)
      hzstarbasin hev
  have hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z) := fun z hz => by
    rw [hββ₁ hz]; exact hβ₁mod z hz
  refine ⟨β, hβan, hβesc, hβmod, fun z₀ hz₀ => ?_⟩
  exact not_continuesAcross_beta_of_connected_package hc0 hc2 hconn hz₀ hβmod hψan hψβ
    hhd hhe hfe hh0 hbridge

/-- **`hnb` for ANY branch matching `bottcherCoord` on `escapeOpen`.** The crux natural boundary holds
not just for the canonical disk-model branch but for *every* `β` analytic on the basin that agrees with
`bottcherCoord c₁` on `escapeOpen c₁`: such a `β` equals the canonical branch on the whole (preconnected)
basin by the identity theorem, and `ContinuesAcross β (filledJulia c₁)ᶜ z₀` only reads `β` on the basin
side, so it transfers. This is the form the rigidity engine
`noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable` consumes — it lets the engine's
*own* branch `β` receive `hnb` for free, removing `hnb` from the caller's obligations for every connected
`c₁ ∈ mandelbrot ∖ {0,-2}` (#118). -/
theorem hnb_of_branch_matching {c₁ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) :
    ∀ z₀ ∈ frontier (filledJulia c₁),
      ¬ U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  obtain ⟨β', hβ'an, hβ'esc, hβ'mod, hnb'⟩ :=
    hnb_of_mem_mandelbrot_connected hc₁M hc₁0 hc₁2 hconn₁
  obtain ⟨zstar, hzstar⟩ : (escapeOpen c₁).Nonempty := ⟨_, deepPoint_mem_escapeOpen c₁⟩
  have hzstarbasin : zstar ∈ (filledJulia c₁)ᶜ := escapeOpen_subset_compl_filledJulia c₁ hzstar
  have hev : β =ᶠ[𝓝 zstar] β' := by
    filter_upwards [(isOpen_escapeOpen c₁).mem_nhds hzstar] with z hz
    rw [hβesc z hz, hβ'esc z hz]
  have hββ' : Set.EqOn β β' (filledJulia c₁)ᶜ :=
    hβan.eqOn_of_preconnected_of_eventuallyEq hβ'an (isPreconnected_compl_filledJulia c₁)
      hzstarbasin hev
  intro z₀ hz₀ hca
  apply hnb' z₀ hz₀
  obtain ⟨g, hgAt, hgβev⟩ := hca
  refine ⟨g, hgAt, ?_⟩
  filter_upwards [hgβev, self_mem_nhdsWithin] with w hgw hwc
  rw [hgw, hββ' hwc]

end Bottcher
