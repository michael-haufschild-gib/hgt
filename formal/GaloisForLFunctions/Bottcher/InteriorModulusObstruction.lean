/-
# Interior-nonempty natural-boundary: the open-nodal-set dichotomy branch (toward #118)

Toward `hnb` for interior-NONEMPTY connected `c₁` (hyperbolic-component parameters), the discharge of
`ComponentSideNoncontinuabilityOnJulia` splits on the nodal set `{u = 0}` of `u := log‖g‖`, where `g`
is a hypothetical analytic continuation of the Böttcher branch across a frontier point. This file
supplies the EASY branch of that dichotomy: if `‖g‖ ≡ 1` on a nonempty open set, then `g` is constant,
contradicting `g = φ_{c₁}` being nonconstant on the basin side (`‖φ‖ = exp(G) > 1`). The hard branch
(the nodal arc is real-analytic ⟹ `J_{c₁}` locally analytic ⟹ `c₁ ∈ {0,-2}` via the proven even-FE
`c_mem_of_even_holo_ball`) is handled separately.

Axiom-clean; pure complex analysis (strong maximum modulus + identity theorem).
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness
import GaloisForLFunctions.Bottcher.DendriteContinuesAcross

open Complex Metric Set Topology Filter

namespace Bottcher

/-- **Constant modulus forces constant.** An analytic (`DifferentiableOn ℂ`) function whose modulus is
constant on a preconnected open set is itself constant there — the strong maximum modulus principle
read through a trivial `IsMaxOn`. -/
theorem eqOn_const_of_norm_const {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (hc : c ∈ U)
    (hconst : ∀ z ∈ U, ‖f z‖ = ‖f c‖) : Set.EqOn f (fun _ => f c) U := by
  apply eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hf hc
  intro z hz
  exact le_of_eq (hconst z hz)

/-- **The open-nodal-set obstruction.** If `g` is analytic on a preconnected open set `U`, its modulus
is `1` on a nonempty open subset `V ⊆ U`, and `‖g‖ ≠ 1` at some point of `U`, then `False`. On a ball
inside `V` the modulus is constant, so `g` is locally constant; the identity theorem spreads the
constant to all of `U`, forcing `‖g‖ ≡ 1` on `U` — contradicting the witness. This is the `u ≡ 0`
branch of the nodal-set dichotomy for the interior-nonempty natural boundary (#118): a hypothetical
continuation `g` of `φ_{c₁}` cannot have `‖g‖ ≡ 1` on an open piece of `interior K_{c₁}` while equaling
the nonconstant `φ_{c₁}` on the basin side. -/
theorem false_of_norm_one_on_open_of_norm_ne
    {g : ℂ → ℂ} {U V : Set ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hVU : V ⊆ U) (hVo : IsOpen V) {v₀ : ℂ} (hv₀ : v₀ ∈ V)
    (hV1 : ∀ z ∈ V, ‖g z‖ = 1)
    {z₁ : ℂ} (hz₁U : z₁ ∈ U) (hz₁ : ‖g z₁‖ ≠ 1) : False := by
  have hgv₀ : ‖g v₀‖ = 1 := hV1 v₀ hv₀
  have hv₀U : v₀ ∈ U := hVU hv₀
  -- a ball around `v₀` inside `V`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo v₀ hv₀
  have hBU : ball v₀ ε ⊆ U := hball.trans hVU
  -- `g` is constant `g v₀` on that ball (constant modulus + strong max modulus)
  have hgconstB : Set.EqOn g (fun _ => g v₀) (ball v₀ ε) := by
    apply eqOn_const_of_norm_const (convex_ball v₀ ε).isPreconnected isOpen_ball
      (hg.mono hBU) (mem_ball_self hε)
    intro z hz
    rw [hV1 z (hball hz), hgv₀]
  -- spread the constant to all of `U` by the identity theorem
  have hgA : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hUo
  have hconstA : AnalyticOnNhd ℂ (fun _ : ℂ => g v₀) U := analyticOnNhd_const
  have hev : g =ᶠ[𝓝 v₀] (fun _ => g v₀) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hgconstB hz
  have hEqU : Set.EqOn g (fun _ => g v₀) U :=
    hgA.eqOn_of_preconnected_of_eventuallyEq hconstA hUc hv₀U hev
  exact hz₁ (by rw [hEqU hz₁U]; exact hgv₀)

/-- **A continuation across a frontier point has modulus one.** If `β` carries the Böttcher modulus
`‖β z‖ = exp(G_c z)` on the basin `(filledJulia c)ᶜ` and `g` is an analytic continuation of `β` across
a frontier point `z₀` (`g` analytic at `z₀`, `g = β` on a basin-side neighborhood), then
`‖g z₀‖ = 1`: the frontier is the unit-modulus level `G_c = 0`. Unconditional foundational brick for
the interior-nonempty natural boundary (#118): whatever `g` does inside `K`, its modulus at the
frontier point is pinned to `1`. -/
theorem norm_continuation_eq_one_at_frontier {c z₀ : ℂ} {β g : ℂ → ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hfront : z₀ ∈ frontier (filledJulia c))
    (hgAt : AnalyticAt ℂ g z₀)
    (hgEq : ∀ᶠ w in 𝓝[(filledJulia c)ᶜ] z₀, g w = β w) :
    ‖g z₀‖ = 1 := by
  haveI hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    nhdsWithin_compl_filledJulia_neBot_of_frontier hfront
  -- on the basin side, `‖g‖ = exp(G_c)`
  have hmod : ∀ᶠ w in 𝓝[(filledJulia c)ᶜ] z₀,
      ‖g w‖ = Real.exp (greenFunctionDyn c w) := by
    filter_upwards [hgEq, self_mem_nhdsWithin] with w hw hwc
    rw [hw, hβmod w hwc]
  -- `‖g ·‖ → ‖g z₀‖` by continuity of the continuation
  have h1 : Tendsto (fun w => ‖g w‖) (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 ‖g z₀‖) :=
    (hgAt.continuousAt.norm).continuousWithinAt.tendsto
  -- `exp(G_c ·) → exp(G_c z₀)` and `‖g ·‖` shares that limit
  have h2 : Tendsto (fun w => Real.exp (greenFunctionDyn c w))
      (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 (Real.exp (greenFunctionDyn c z₀))) :=
    ((Real.continuous_exp.comp (continuous_greenFunctionDyn c)).continuousAt).continuousWithinAt.tendsto
  have h3 : Tendsto (fun w => ‖g w‖) (𝓝[(filledJulia c)ᶜ] z₀)
      (𝓝 (Real.exp (greenFunctionDyn c z₀))) := h2.congr' (Filter.EventuallyEq.symm hmod)
  have hgz0 : greenFunctionDyn c z₀ = 0 :=
    (greenFunctionDyn_eq_zero_iff c z₀).mpr (mem_filledJulia_of_frontier hfront)
  have heq := tendsto_nhds_unique h1 h3
  rw [heq, hgz0, Real.exp_zero]

/-- **The Böttcher-wired `u ≡ 0` obstruction.** Let `g` be an analytic continuation of the Böttcher
branch `β` on a preconnected open `U` containing a frontier point `z₀` (with `g = β` on the basin part
of `U`). If `‖g‖ ≡ 1` on some nonempty open `V ⊆ U`, then `False`. The basin side of `U` supplies a
witness `z₁` with `‖g z₁‖ = exp(G_c z₁) > 1`, and `false_of_norm_one_on_open_of_norm_ne` closes it.
This is the `u ≡ 0` branch of the interior-nonempty natural-boundary dichotomy (#118) in the concrete
Böttcher setting: a continuation cannot have modulus `1` on an open piece of `interior K_{c₁}`. -/
theorem false_of_continuation_norm_one_on_open {c z₀ : ℂ} {β g : ℂ → ℂ} {U V : Set ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hz₀U : z₀ ∈ U)
    (hg : DifferentiableOn ℂ g U)
    (hgβ : ∀ z ∈ U ∩ (filledJulia c)ᶜ, g z = β z)
    (hfront : z₀ ∈ frontier (filledJulia c))
    (hVU : V ⊆ U) (hVo : IsOpen V) {v₀ : ℂ} (hv₀ : v₀ ∈ V)
    (hV1 : ∀ z ∈ V, ‖g z‖ = 1) : False := by
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    nhdsWithin_compl_filledJulia_neBot_of_frontier hfront
  -- a basin point of `U` near `z₀`
  obtain ⟨z₁, hz₁U, hz₁Kc⟩ : ∃ z₁, z₁ ∈ U ∧ z₁ ∈ (filledJulia c)ᶜ := by
    obtain ⟨z, hz⟩ := hNeBot.nonempty_of_mem
      (inter_mem (mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hz₀U)) self_mem_nhdsWithin)
    exact ⟨z, hz.1, hz.2⟩
  -- there `‖g‖ = exp(G_c) > 1`, so `‖g‖ ≠ 1`
  have hGpos : 0 < greenFunctionDyn c z₁ := by
    rcases (greenFunctionDyn_nonneg c z₁).lt_or_eq with h | h
    · exact h
    · exact absurd ((greenFunctionDyn_eq_zero_iff c z₁).mp h.symm) hz₁Kc
  have hgz₁ : ‖g z₁‖ = Real.exp (greenFunctionDyn c z₁) := by
    rw [hgβ z₁ ⟨hz₁U, hz₁Kc⟩, hβmod z₁ hz₁Kc]
  have hz₁ne : ‖g z₁‖ ≠ 1 := by
    rw [hgz₁]
    have : (1 : ℝ) < Real.exp (greenFunctionDyn c z₁) := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hGpos
    exact ne_of_gt this
  exact false_of_norm_one_on_open_of_norm_ne hUc hUo hg hVU hVo hv₀ hV1 hz₁U hz₁ne

end Bottcher
