/-
# The full-unit-disk Böttcher model `h(t) = t·ψ(1/t)` for `c ∈ mandelbrot`

Gap 2 gave the unconditional branch `β` and `BasinGlobalInverse` its global analytic inverse `ψ` on
the exterior `{1 < ‖w‖}`. This file assembles the **disk model on the whole unit disk**: analytic,
even, satisfying the model functional equation `h(t²) = h(t)² + c·t²`, normalized `h(0) = 1`, and
explicitly bridged to the basin (`h t = t·ψ(1/t)` for `t ≠ 0`). Near `0` it agrees with the far-field
model of `BottcherFarFieldSurjective.exists_disk_model` (via uniqueness of the inverse), which
supplies the removable singularity at `0` and the even/FE identities on a small annulus; the identity
theorem on the convex ball then propagates them to the whole disk.

This is the object whose natural boundary (`natural_boundary_of_even_fe`) the connected-case
transcendence contradicts.
-/
import GaloisForLFunctions.Bottcher.BasinGlobalInverse
import GaloisForLFunctions.Bottcher.BottcherFarFieldSurjective
open Complex Set Metric Filter Topology Bornology
namespace Bottcher
noncomputable section

/-- **The full-disk model with basin bridge.** For `c ∈ mandelbrot`: `h` analytic on `ball 0 1`,
even, FE-solution, `h 0 = 1`, with `h t = t·ψ(1/t)` and `β, ψ` the mutually inverse branch pair of
`BasinGlobalInverse`. -/
theorem exists_full_disk_model_of_mem_mandelbrot (c : ℂ) (hcM : c ∈ mandelbrot) :
    ∃ (h β ψ : ℂ → ℂ),
      DifferentiableOn ℂ h (ball 0 1) ∧
      (∀ t ∈ ball (0:ℂ) 1, h (-t) = h t) ∧
      (∀ t ∈ ball (0:ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2) ∧
      h 0 = 1 ∧
      (∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) ∧
      AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      AnalyticOnNhd ℂ ψ {w : ℂ | 1 < ‖w‖} ∧
      (∀ w : ℂ, 1 < ‖w‖ → ψ w ∈ (filledJulia c)ᶜ) ∧
      (∀ w : ℂ, 1 < ‖w‖ → β (ψ w) = w) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z) := by
  classical
  obtain ⟨β, ψ, hβan, hβesc, hβmod, hβgt, hβfe, hψan, hψmem, hβψ, hψβ⟩ :=
    exists_global_branch_with_inverse_of_mem_mandelbrot c hcM
  -- far-field radius
  set R : ℝ := 2 * max 2 ‖c‖ + 16 * ‖c‖ + 1 with hRdef
  have hcnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hmax2 : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
  have hR1 : 2 * max 2 ‖c‖ < R := by rw [hRdef]; linarith
  have hRgt1 : (1:ℝ) < R := by rw [hRdef]; linarith
  have hR2 : 16 * ‖c‖ < R ^ 2 := by
    have h16R : 16 * ‖c‖ + 1 ≤ R := by rw [hRdef]; linarith
    nlinarith
  have hRpos : (0:ℝ) < R := by linarith
  obtain ⟨ψf, hψfleft, _hψfan, _hψfright⟩ := exists_analytic_inverse_far hR1 hR2
  obtain ⟨R', hRpre⟩ := exists_bottcher_far_preimage hR1 hR2
  set S : ℝ := max R' 1 with hSdef
  have hSpos : (0:ℝ) < S := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hS1 : (1:ℝ) ≤ S := le_max_right _ _
  -- global ψ agrees with the far inverse beyond S
  have hagree : ∀ w : ℂ, S < ‖w‖ → ψ w = ψf w := by
    intro w hw
    obtain ⟨z, hzR, hzw⟩ := hRpre w (lt_of_le_of_lt (le_max_left R' 1) hw)
    have hzesc : z ∈ escapeOpen c := by
      show max 2 ‖c‖ < ‖z‖
      calc max 2 ‖c‖ < 2 * max 2 ‖c‖ := by nlinarith [lt_of_lt_of_le two_pos hmax2]
        _ < R := hR1
        _ < ‖z‖ := hzR
    have hzbasin : z ∈ (filledJulia c)ᶜ := escapeOpen_subset_compl_filledJulia c hzesc
    have hβz : β z = w := by rw [hβesc z hzesc, hzw]
    have h1 : ψ w = z := by rw [← hβz, hψβ z hzbasin]
    have h2 : ψf w = z := by rw [← hzw, hψfleft z hzR]
    rw [h1, h2]
  -- asymptotics of the global inverse
  have htendf : Tendsto (fun w => ψf w - w) (cobounded ℂ) (𝓝 0) :=
    tendsto_psi_sub_id hR1 hR2 hψfleft
  have hevS : ∀ᶠ w : ℂ in cobounded ℂ, S < ‖w‖ := by
    have := tendsto_norm_cobounded_atTop (E := ℂ)
    exact this.eventually (eventually_gt_atTop S)
  have htend : Tendsto (fun w => ψ w - w) (cobounded ℂ) (𝓝 0) := by
    refine htendf.congr' ?_
    filter_upwards [hevS] with w hw
    rw [hagree w hw]
  -- the model
  set h₀ : ℂ → ℂ := fun t => t * ψ (1 / t) with hh₀def
  set h : ℂ → ℂ := Function.update h₀ 0 1 with hhdef
  have hinvbig : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → 1 < ‖(1:ℂ) / t‖ := by
    intro t ht0 htR
    have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    rw [one_div, norm_inv]
    exact (lt_inv_comm₀ one_pos htn).mpr (by simpa using htR)
  have hdon : DifferentiableOn ℂ h₀ (ball 0 1 \ {0}) := by
    intro t ht
    have ht0 : t ≠ 0 := fun hc' => ht.2 (by simp [hc'])
    have htR : ‖t‖ < 1 := by rw [← mem_ball_zero_iff]; exact ht.1
    have hbig := hinvbig t ht0 htR
    have hψd : DifferentiableAt ℂ ψ (1 / t) := (hψan (1 / t) hbig).differentiableAt
    have hinvd : DifferentiableAt ℂ (fun t : ℂ => 1 / t) t :=
      (differentiableAt_const (1:ℂ)).div differentiableAt_id ht0
    exact ((differentiableAt_id).mul (hψd.comp t hinvd)).differentiableWithinAt
  have hballnhds : ball (0:ℂ) 1 ∈ 𝓝 (0:ℂ) := isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have hcong : Set.EqOn h h₀ (ball (0:ℂ) 1 \ {0}) := by
    intro t ht
    have ht0 : t ≠ 0 := fun hc' => ht.2 (by simp [hc'])
    exact Function.update_of_ne ht0 _ _
  have hlim1 : Tendsto h₀ (𝓝[≠] 0) (𝓝 1) := model_tendsto_one htend
  have hcont0 : ContinuousAt h 0 := continuousAt_update_same.mpr hlim1
  have hdisk : DifferentiableOn ℂ h (ball 0 1) :=
    (differentiableOn_compl_singleton_and_continuousAt_iff hballnhds).mp
      ⟨hdon.congr hcong, hcont0⟩
  have hupd : ∀ t : ℂ, t ≠ 0 → h t = t * ψ (1 / t) := by
    intro t ht0
    rw [hhdef]; rw [Function.update_of_ne ht0]
  have hh0 : h 0 = 1 := by rw [hhdef]; exact Function.update_self 0 1 h₀
  -- far-field annulus where h matches the far model
  set ε : ℝ := 1 / (S + 1) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεlt1 : ε < 1 := by
    rw [hεdef, div_lt_one (by linarith)]; linarith
  have hfarS : ∀ t : ℂ, t ≠ 0 → ‖t‖ < ε → S < ‖(1:ℂ)/t‖ := by
    intro t ht0 htε
    have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    rw [one_div, norm_inv]
    have : ‖t‖ < 1/(S+1) := by rw [← hεdef]; exact htε
    have h2 : S + 1 < ‖t‖⁻¹ := by
      rw [lt_inv_comm₀ (by linarith) htn]
      rw [inv_eq_one_div]; exact this
    linarith
  -- ψf is odd and satisfies FE beyond S (transfer from exists_far_inverse-style lemmas)
  have hψffe : ∀ w : ℂ, S < ‖w‖ → ψf (w ^ 2) = (ψf w) ^ 2 + c := by
    intro w hw
    obtain ⟨z, hzR, hzw⟩ := hRpre w (lt_of_le_of_lt (le_max_left R' 1) hw)
    rw [← hzw]
    exact psi_functional_eq_of_inverts hR1 hR2 hψfleft z hzR
  have hψfodd : ∀ w : ℂ, S < ‖w‖ → ψf (-w) = -ψf w := by
    intro w hw
    obtain ⟨z, hzR, hzw⟩ := hRpre w (lt_of_le_of_lt (le_max_left R' 1) hw)
    rw [← hzw]
    exact psi_odd_of_inverts hRpos.le hψfleft z hzR
  -- h even and FE on the annulus 0<‖t‖<ε
  have hmodel : ∀ t : ℂ, t ≠ 0 → ‖t‖ < ε →
      ((-t) * ψf (1 / -t) = t * ψf (1 / t) ∧
       (t ^ 2) * ψf (1 / t ^ 2) = (t * ψf (1 / t)) ^ 2 + c * t ^ 2) := by
    intro t ht0 htε
    have hSinv : ‖t‖ < S⁻¹ := by
      have h1 : S < ‖(1:ℂ)/t‖ := hfarS t ht0 htε
      rw [one_div, norm_inv] at h1
      exact (lt_inv_comm₀ hSpos (norm_pos_iff.mpr ht0)).mp h1
    exact model_even_and_fe hSpos (fun w hw => hψfodd w hw) (fun w hw => hψffe w hw) t ht0 hSinv
  -- transfer h₀ = t ψf(1/t) on annulus
  have hh₀far : ∀ t : ℂ, t ≠ 0 → ‖t‖ < ε → h t = t * ψf (1 / t) := by
    intro t ht0 htε
    rw [hupd t ht0, hagree (1/t) (hfarS t ht0 htε)]
  -- EVEN on annulus
  have hevenann : ∀ t : ℂ, t ≠ 0 → ‖t‖ < ε → h (-t) = h t := by
    intro t ht0 htε
    have hnt0 : -t ≠ 0 := neg_ne_zero.mpr ht0
    have hntε : ‖-t‖ < ε := by rwa [norm_neg]
    rw [hh₀far (-t) hnt0 hntε, hh₀far t ht0 htε]
    exact (hmodel t ht0 htε).1
  -- FE on annulus
  have hfeann : ∀ t : ℂ, t ≠ 0 → ‖t‖ < ε → h (t ^ 2) = (h t) ^ 2 + c * t ^ 2 := by
    intro t ht0 htε
    have ht20 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    have ht2ε : ‖t ^ 2‖ < ε := by
      rw [norm_pow]
      calc ‖t‖ ^ 2 ≤ ‖t‖ * 1 := by nlinarith [norm_nonneg t, htε, hεlt1]
        _ = ‖t‖ := mul_one _
        _ < ε := htε
    rw [hh₀far (t^2) ht20 ht2ε, hh₀far t ht0 htε]
    exact (hmodel t ht0 htε).2
  -- identity theorem: even and FE propagate to the whole ball
  have hAan : AnalyticOnNhd ℂ h (ball 0 1) := hdisk.analyticOnNhd isOpen_ball
  set t₀ : ℂ := ((ε/2 : ℝ) : ℂ) with ht₀def
  have ht₀norm : ‖t₀‖ = ε/2 := by
    rw [ht₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have ht₀0 : t₀ ≠ 0 := by
    intro hcon; rw [hcon, norm_zero] at ht₀norm; linarith
  have ht₀ball : t₀ ∈ ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff, ht₀norm]; linarith
  -- even everywhere
  have heven : ∀ t ∈ ball (0:ℂ) 1, h (-t) = h t := by
    have h1 : AnalyticOnNhd ℂ (fun t => h (-t)) (ball 0 1) := by
      intro t ht
      have hnt : -t ∈ ball (0:ℂ) 1 := by rw [mem_ball_zero_iff, norm_neg]; rwa [mem_ball_zero_iff] at ht
      exact (hAan (-t) hnt).comp ((analyticAt_id.neg : AnalyticAt ℂ (fun z : ℂ => -z) t))
    have hev : (fun t => h (-t)) =ᶠ[𝓝 t₀] h := by
      have hball : Metric.ball t₀ (ε/2) ∈ 𝓝 t₀ := isOpen_ball.mem_nhds (mem_ball_self (by linarith))
      filter_upwards [hball] with t ht
      have htnorm : ‖t‖ < ε := by
        have := mem_ball.mp ht
        calc ‖t‖ = ‖t₀ + (t - t₀)‖ := by ring_nf
          _ ≤ ‖t₀‖ + ‖t - t₀‖ := norm_add_le _ _
          _ < ε/2 + ε/2 := by
              rw [ht₀norm]
              have hd : ‖t - t₀‖ < ε/2 := by rw [← dist_eq_norm]; exact mem_ball.mp ht
              linarith
          _ = ε := by ring
      by_cases ht0 : t = 0
      · subst ht0; simp
      · exact hevenann t ht0 htnorm
    exact fun t ht =>
      (h1.eqOn_of_preconnected_of_eventuallyEq hAan (convex_ball 0 1).isPreconnected ht₀ball hev) ht
  -- FE everywhere
  have hfe : ∀ t ∈ ball (0:ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2 := by
    have h1 : AnalyticOnNhd ℂ (fun t => h (t ^ 2)) (ball 0 1) := by
      intro t ht
      have ht2 : t ^ 2 ∈ ball (0:ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_pow]
        rw [mem_ball_zero_iff] at ht
        nlinarith [norm_nonneg t]
      have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ 2) t := (analyticAt_id).pow 2
      show AnalyticAt ℂ (h ∘ fun z : ℂ => z ^ 2) t
      exact AnalyticAt.comp (f := fun z : ℂ => z ^ 2) (x := t) (hAan (t^2) ht2) hsq
    have h2 : AnalyticOnNhd ℂ (fun t => (h t) ^ 2 + c * t ^ 2) (ball 0 1) := by
      intro t ht
      have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ 2) t := (analyticAt_id).pow 2
      exact ((hAan t ht).pow 2).add ((analyticAt_const).mul hsq)
    have hev : (fun t => h (t ^ 2)) =ᶠ[𝓝 t₀] (fun t => (h t) ^ 2 + c * t ^ 2) := by
      have hball : Metric.ball t₀ (ε/2) ∈ 𝓝 t₀ := isOpen_ball.mem_nhds (mem_ball_self (by linarith))
      filter_upwards [hball] with t ht
      have htnorm : ‖t‖ < ε := by
        calc ‖t‖ = ‖t₀ + (t - t₀)‖ := by ring_nf
          _ ≤ ‖t₀‖ + ‖t - t₀‖ := norm_add_le _ _
          _ < ε/2 + ε/2 := by
              rw [ht₀norm]
              have hd : ‖t - t₀‖ < ε/2 := by rw [← dist_eq_norm]; exact mem_ball.mp ht
              linarith
          _ = ε := by ring
      by_cases ht0 : t = 0
      · subst ht0; simp [hh0]
      · exact hfeann t ht0 htnorm
    exact fun t ht =>
      (h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_ball 0 1).isPreconnected ht₀ball hev) ht
  exact ⟨h, β, ψ, hdisk, heven, hfe, hh0,
    (fun t ht0 ht1 => hupd t ht0), hβan, hβesc, hψan, hψmem, hβψ, hψβ⟩

end
end Bottcher
