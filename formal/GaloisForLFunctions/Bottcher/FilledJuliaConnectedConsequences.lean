/-
# Discharging the `IsPreconnected (filledJulia c)` hypothesis for `c ∈ mandelbrot`

`isPreconnected_filledJulia` (proved in `FilledJuliaConnected`) lets the connected-case perfect-set /
frontier / countable-avoidance results of `JuliaFrontierPerfect` drop their standing hypothesis
`hconn : IsPreconnected (filledJulia c)` in favour of the intrinsic parameter condition
`c ∈ mandelbrot`. Each corollary here is the corresponding `JuliaFrontierPerfect` theorem with `hconn`
supplied.
-/
import GaloisForLFunctions.Bottcher.FilledJuliaConnected
import GaloisForLFunctions.Bottcher.JuliaFrontierPerfect

namespace Bottcher

/-- **The filled Julia set of a Mandelbrot parameter is a perfect set.** No separate connectedness
hypothesis: `c ∈ mandelbrot` gives `IsPreconnected (filledJulia c)` (`isPreconnected_filledJulia`),
and `K_c` is always nontrivial (`filledJulia_nontrivial`). -/
theorem perfect_filledJulia_of_mem_mandelbrot {c : ℂ} (hc : c ∈ mandelbrot) :
    Perfect (filledJulia c) :=
  perfect_filledJulia_of_preconnected_nontrivial (isPreconnected_filledJulia hc)
    (filledJulia_nontrivial c)

/-- Frontier of a Mandelbrot-parameter filled Julia set with empty interior is perfect. -/
theorem perfect_frontier_filledJulia_of_mem_mandelbrot_emptyInterior {c : ℂ}
    (hc : c ∈ mandelbrot) (hempty : interior (filledJulia c) = ∅) :
    Perfect (frontier (filledJulia c)) :=
  perfect_frontier_filledJulia_of_preconnected_emptyInterior (isPreconnected_filledJulia hc) hempty

/-- Uncountable local frontier for a Mandelbrot parameter with empty interior. -/
theorem not_countable_ball_inter_frontier_filledJulia_of_mem_mandelbrot_emptyInterior
    {c p : ℂ} (hc : c ∈ mandelbrot) (hempty : interior (filledJulia c) = ∅)
    (hp : p ∈ filledJulia c) {r : ℝ} (hr : 0 < r) :
    ¬ (Metric.ball p r ∩ frontier (filledJulia c)).Countable :=
  not_countable_ball_inter_frontier_filledJulia_of_preconnected_emptyInterior
    (isPreconnected_filledJulia hc) hempty hp hr

/-- Local frontier target-set package (countable avoidance / closure / off-other) for a Mandelbrot
parameter — the connected hRigid lane input, with `hconn` discharged. -/
theorem exists_local_frontier_target_set_of_mem_mandelbrot_emptyInterior
    {U Ω : Set ℂ} {c₁ c₂ : ℂ} (hc₁ : c₁ ∈ mandelbrot)
    (hempty : interior (filledJulia c₁) = ∅)
    {p : ℂ} (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    {rLocal rOther : ℝ} (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ Metric.ball p rLocal ∧ z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ) :=
  exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
    (isPreconnected_filledJulia hc₁) hempty hpK hpΩ hrLocal hrOther hsector hother

end Bottcher
