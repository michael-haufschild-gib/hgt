/-
# The Böttcher natural boundary from a single access region

For connected `c ∉ {0,-2}` let `β` be the global Böttcher branch on the basin `Ω_c = K_cᶜ` and `ψ`
its inverse on `{|w| > 1}`.  If some holomorphic `g` with `g'(z₀) ≠ 0` at a Julia point `z₀` agrees
with `β` merely on an open set `A ⊆ Ω_c` accumulating at `z₀` — one access region, not a full basin
neighbourhood — the contradiction still follows.

The point is to argue in the `w`-plane.  Near `w₀ = g(z₀)`, on the unit circle, the local inverse
`γ` of `g` agrees with `ψ` on the open set `g(A)` of the lune `ball w₀ ε ∩ {|w| > 1}`: for `z ∈ A`,
`γ(g z) = z = ψ(β z) = ψ(g z)`.  The lune is connected, whatever the geometry of `Ω_c` near `z₀`, so
`γ = ψ` on the whole lune and `ψ` continues across an arc of the circle.  Through the disk model
`h(t) = t ψ(1/t)` this is an analytic continuation of `h` across an arc, which the natural boundary
of the even Böttcher functional equation forbids.
-/
import GaloisForLFunctions.Bottcher.InteriorModulusObstruction

open Complex Metric Set Topology Filter

namespace Bottcher

/-- **The seed agreement from an open access region.**  With `g = β` on an open `A ⊆ Ω_c` whose
closure contains `z₀`, the local inverse `γ` of `g` agrees with `ψ` on a neighbourhood of some point
of the exterior lune at `w₀ = g z₀`. -/
theorem exists_seed_of_open_approach
    {c : ℂ} {β ψ g γ : ℂ → ℂ} {z₀ w₀ : ℂ} {ε : ℝ} {A : Set ℂ}
    (hε : 0 < ε)
    (hgAt : AnalyticAt ℂ g z₀) (hw₀ : g z₀ = w₀)
    (hγAn : AnalyticOnNhd ℂ γ (Metric.ball w₀ ε))
    (hγg : ∀ᶠ z in 𝓝 z₀, γ (g z) = z)
    (hgγ : ∀ᶠ w in 𝓝 w₀, g (γ w) = w)
    (hAo : IsOpen A) (hAK : A ⊆ (filledJulia c)ᶜ) (hz₀A : z₀ ∈ closure A)
    (hgA : ∀ z ∈ A, g z = β z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z) :
    ∃ w₁, w₁ ∈ Metric.ball w₀ ε ∩ {w : ℂ | 1 < ‖w‖} ∧ γ =ᶠ[𝓝 w₁] ψ := by
  haveI hne : (𝓝[A] z₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz₀A
  have hgcont : ContinuousAt g z₀ := hgAt.continuousAt
  obtain ⟨O₀, hO₀sub, hO₀op, hw₀O₀⟩ := _root_.mem_nhds_iff.mp hgγ
  have hgO₀ : ∀ᶠ z in 𝓝 z₀, g z ∈ O₀ := hgcont (hw₀ ▸ hO₀op.mem_nhds hw₀O₀)
  have hgball : ∀ᶠ z in 𝓝 z₀, g z ∈ Metric.ball w₀ ε :=
    hgcont (hw₀ ▸ Metric.ball_mem_nhds w₀ hε)
  have key : ∀ᶠ z in 𝓝[A] z₀,
      z ∈ A ∧ γ (g z) = z ∧ g z ∈ O₀ ∧ g z ∈ Metric.ball w₀ ε := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hγg, nhdsWithin_le_nhds hgO₀,
      nhdsWithin_le_nhds hgball] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨z₁, hz₁A, hγz₁, hgz₁O, hgz₁ball⟩ := key.exists
  have hz₁K : z₁ ∈ (filledJulia c)ᶜ := hAK hz₁A
  have hGpos : 0 < greenFunctionDyn c z₁ := by
    rcases (greenFunctionDyn_nonneg c z₁).lt_or_eq with h | h
    · exact h
    · exact absurd ((greenFunctionDyn_eq_zero_iff c z₁).mp h.symm) hz₁K
  have hw₁norm : 1 < ‖g z₁‖ := by
    rw [hgA z₁ hz₁A, hβmod z₁ hz₁K]
    exact Real.one_lt_exp_iff.mpr hGpos
  refine ⟨g z₁, ⟨hgz₁ball, hw₁norm⟩, ?_⟩
  -- near `g z₁`, the local inverse lands in `A`
  have hγcont : ContinuousAt γ (g z₁) :=
    (hγAn (g z₁) hgz₁ball).continuousAt
  have hγA : ∀ᶠ w in 𝓝 (g z₁), γ w ∈ A := by
    have : A ∈ 𝓝 (γ (g z₁)) := by rw [hγz₁]; exact hAo.mem_nhds hz₁A
    exact hγcont this
  filter_upwards [hγA, hO₀op.mem_nhds hgz₁O] with w hwA hwO
  have hgw : g (γ w) = w := hO₀sub hwO
  have hβw : β (γ w) = w := by rw [← hgA (γ w) hwA, hgw]
  calc γ w = ψ (β (γ w)) := (hψβ (γ w) (hAK hwA)).symm
    _ = ψ w := by rw [hβw]

/-- **Natural boundary of the Böttcher branch from one access region.**  For `c ∉ {0,-2}`, with the
connected Böttcher package, no holomorphic `g` with `g'(z₀) ≠ 0` at a frontier point `z₀` of `K_c`
agrees with the Böttcher branch on an open access region `A ⊆ Ω_c` with `z₀ ∈ closure A`. -/
theorem false_of_continuation_on_open_approach
    {c z₀ : ℂ} {β ψ h g : ℂ → ℂ} {A : Set ℂ}
    (hc0 : c ≠ 0) (hc2 : c ≠ -2)
    (hz₀front : z₀ ∈ frontier (filledJulia c))
    (hgAt : AnalyticAt ℂ g z₀) (hd0 : deriv g z₀ ≠ 0)
    (hAo : IsOpen A) (hAK : A ⊆ (filledJulia c)ᶜ) (hz₀A : z₀ ∈ closure A)
    (hgA : ∀ z ∈ A, g z = β z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψan : AnalyticOnNhd ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ t ∈ ball (0:ℂ) 1, h (-t) = h t)
    (hfe : ∀ t ∈ ball (0:ℂ) 1, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (hh0 : h 0 = 1)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    False := by
  haveI hne : (𝓝[A] z₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz₀A
  -- the continuation has modulus one at the Julia point
  have hz₀K : z₀ ∈ filledJulia c := mem_filledJulia_of_frontier hz₀front
  have hG0 : greenFunctionDyn c z₀ = 0 := (greenFunctionDyn_eq_zero_iff c z₀).mpr hz₀K
  have hw₀norm : ‖g z₀‖ = 1 := by
    have hlim1 : Tendsto (fun z => ‖g z‖) (𝓝[A] z₀) (𝓝 ‖g z₀‖) :=
      (hgAt.continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
    have hGc : Tendsto (fun z => Real.exp (greenFunctionDyn c z)) (𝓝[A] z₀)
        (𝓝 (Real.exp (greenFunctionDyn c z₀))) :=
      (((Real.continuous_exp.comp (continuous_greenFunctionDyn c)).tendsto z₀)).mono_left
        nhdsWithin_le_nhds
    rw [hG0, Real.exp_zero] at hGc
    have hlim2 : Tendsto (fun z => ‖g z‖) (𝓝[A] z₀) (𝓝 1) := by
      refine hGc.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hgA z hz, hβmod z (hAK hz)]
    exact tendsto_nhds_unique hlim1 hlim2
  have hw₀ne : g z₀ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw₀norm; norm_num at hw₀norm
  obtain ⟨γ, hγAn, hleft, hright⟩ := exists_localInverse_of_continuation hgAt hd0
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.eventually_nhds_iff.mp hγAn.eventually_analyticAt
  set ε : ℝ := min ε₀ (1/2) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hε2 : ε ≤ 1/2 := min_le_right _ _
  have hγAnOn : AnalyticOnNhd ℂ γ (Metric.ball (g z₀) ε) := fun w hw =>
    hball₀ (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
  obtain ⟨w₁, hw₁, hseed⟩ :=
    exists_seed_of_open_approach hε hgAt rfl hγAnOn hleft hright hAo hAK hz₀A hgA hβmod hψβ
  have hγψ : ∀ᶠ w in 𝓝 (g z₀), 1 < ‖w‖ → γ w = ψ w :=
    eqOn_lune_of_seed hw₀norm hε hε2 hγAnOn (fun w hw => hψan w hw.2) hw₁ hseed
  set t₀ : ℂ := 1 / g z₀ with ht₀def
  have htw : t₀ * g z₀ = 1 := by rw [ht₀def, one_div, inv_mul_cancel₀ hw₀ne]
  have ht₀norm : ‖t₀‖ = 1 := by rw [ht₀def, norm_div, norm_one, hw₀norm, div_one]
  have hcont : ContinuesAcross h t₀ := continuesAcross_h_of_localInverse htw hγAn hγψ hbridge
  obtain ⟨r, hr, harc⟩ := arc_of_continuesAcross hcont
  exact natural_boundary_of_even_fe hc0 hc2 ht₀norm hr hhd hhe hfe hh0 harc

end Bottcher
