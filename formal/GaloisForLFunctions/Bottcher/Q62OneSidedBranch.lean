/-
# The branch-route one-sidedness input is exactly `OneSidedAt`

The harmonic Schwarz-reflection route (`BottcherArcExtension.lean`) reduces the both-connected
smooth-piece gatekeeper `SmoothPieceRigidity` to the pure arc geometry `SmoothArcSelection`, using the
generic lune connectivity `isPreconnected_ball_inter_exterior` and *no* branch identification.  The
parallel **branch** route (`Q62SmoothBranchReflection.continuesAcross_of_smoothBranch`) instead
identifies the fibre branch with the Böttcher branch `β` on a *preconnected basin neighbourhood*
`V ∩ K₁ᶜ` and reflects `β`; its one genuinely topological input is that preconnected basin
neighbourhood at the frontier point.

This file pins that input to the tree's already-named ray-landing Prop `OneSidedAt`
(`OneSidedCertificate.lean`, the #133 interface): `OneSidedAt c₁ z₀` *is* the statement that
`ball z₀ ρ \ K₁ = ball z₀ ρ ∩ K₁ᶜ` is connected for small `ρ`, which is precisely the preconnected
basin neighbourhood.  `exists_preconnected_basin_nhd_of_oneSided` extracts it, and
`continuesAcross_of_smoothBranch_oneSided` rebases the branch route on `OneSidedAt`, exhibiting the
branch route's residual as exactly `OneSidedAt` (deep, #133) together with the fibre relation and
non-criticality — the same deep ray-landing content that the `HoleFreeTip` half of the both-connected
case already consumes.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.OneSidedCertificate
import GaloisForLFunctions.Bottcher.Q62SmoothBranchReflection

open Set Metric Filter Topology Complex

namespace Bottcher

/-- **`OneSidedAt` supplies the preconnected basin neighbourhood.**  A one-sided frontier point `z₀`
of `filledJulia c₁` has, for its one-sided radius `ρ₀`, the ball `ball z₀ ρ₀` as an open neighbourhood
whose basin part `ball z₀ ρ₀ ∩ K₁ᶜ` is connected (`ball z₀ ρ₀ \ filledJulia c₁ = ball z₀ ρ₀ ∩ K₁ᶜ`).
This is exactly the preconnected, nonempty basin neighbourhood that the branch route
(`continuesAcross_of_smoothBranch`) consumes as its lone topological input. -/
theorem exists_preconnected_basin_nhd_of_oneSided {c₁ z₀ : ℂ} (hos : OneSidedAt c₁ z₀) :
    ∃ (V : Set ℂ) (ρ₀ : ℝ), 0 < ρ₀ ∧ V = Metric.ball z₀ ρ₀ ∧ IsOpen V ∧ z₀ ∈ V ∧
      IsPreconnected (V ∩ (filledJulia c₁)ᶜ) ∧ (V ∩ (filledJulia c₁)ᶜ).Nonempty := by
  obtain ⟨_hfront, ρ₀, hρ₀, hconn⟩ := hos
  have h := hconn ρ₀ hρ₀ le_rfl
  rw [Set.sdiff_eq] at h
  exact ⟨Metric.ball z₀ ρ₀, ρ₀, hρ₀, rfl, Metric.isOpen_ball, Metric.mem_ball_self hρ₀,
    h.isPreconnected, h.nonempty⟩

/-- **Branch-route Böttcher continuation from `OneSidedAt`.**  The branch route
(`continuesAcross_of_smoothBranch`) rebased on the tree's named one-sidedness Prop.  Given a one-sided
frontier point `z₀` (`OneSidedAt c₁ z₀`), an open neighbourhood `V₀ ∋ z₀` carrying the separated
continuous root family `wfam` with constant fibre degree `N` and the fibre relation for both `wfam` and
`β` on `V₀ ∩ K₁ᶜ`, plus non-criticality of the matched branch at `z₀`, the harmonic reflection
continues `β` across `z₀`.  The one-sided radius shrinks `V₀` to a basin-connected ball, discharging the
preconnected-neighbourhood input purely from `OneSidedAt`; the non-criticality hypothesis is stated in
germ form (`𝓝[K₁ᶜ] z₀`) so it survives the shrink.  This exhibits the branch route's residual as exactly
`OneSidedAt` (#133) ∧ fibre relation ∧ non-criticality. -/
theorem continuesAcross_of_smoothBranch_oneSided
    {c₁ : ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {wfam : Fin N → ℂ → ℂ}
    {β : ℂ → ℂ} {z₀ : ℂ} {V₀ : Set ℂ}
    (hN1 : 1 ≤ N) (hos : OneSidedAt c₁ z₀) (hV₀o : IsOpen V₀) (hz₀V₀ : z₀ ∈ V₀)
    (hwc : ∀ k, ContinuousOn (wfam k) (V₀ ∩ (filledJulia c₁)ᶜ))
    (hβc : ContinuousOn β (V₀ ∩ (filledJulia c₁)ᶜ))
    (hsep : ∀ z ∈ V₀ ∩ (filledJulia c₁)ᶜ, ∀ k l, k ≠ l → wfam k z ≠ wfam l z)
    (hdeg : ∀ z ∈ V₀ ∩ (filledJulia c₁)ᶜ, (fibrePoly a s z).natDegree = N)
    (hwroot : ∀ k, ∀ z ∈ V₀ ∩ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (wfam k z) ^ i = 0)
    (hβrel : ∀ z ∈ V₀ ∩ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hnoncrit : ∀ k, (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z = wfam k z) →
        AnalyticAt ℂ (wfam k) z₀ ∧ deriv (wfam k) z₀ ≠ 0 ∧ ‖wfam k z₀‖ = 1) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  obtain ⟨hz₀front, ρ₀, hρ₀, hconn⟩ := hos
  -- shrink the one-sided radius so the ball lands inside `V₀`
  obtain ⟨r, hr, hrV₀⟩ := Metric.isOpen_iff.mp hV₀o z₀ hz₀V₀
  set ρ : ℝ := min ρ₀ r with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀ hr
  have hballV₀ : Metric.ball z₀ ρ ⊆ V₀ :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hrV₀
  -- the one-sided basin neighbourhood, as a ball inside `V₀`
  have hcball : IsConnected (Metric.ball z₀ ρ \ filledJulia c₁) := hconn ρ hρpos (min_le_left _ _)
  rw [Set.sdiff_eq] at hcball
  set V : Set ℂ := Metric.ball z₀ ρ with hVdef
  have hsub : V ∩ (filledJulia c₁)ᶜ ⊆ V₀ ∩ (filledJulia c₁)ᶜ :=
    Set.inter_subset_inter_left _ hballV₀
  -- the branch route's hypotheses restrict to the shrunken ball
  refine continuesAcross_of_smoothBranch hN1 Metric.isOpen_ball (Metric.mem_ball_self hρpos)
    hcball.isPreconnected hcball.nonempty
    (fun k => (hwc k).mono hsub) (hβc.mono hsub)
    (fun z hz => hsep z (hsub hz)) (fun z hz => hdeg z (hsub hz))
    (fun k z hz => hwroot k z (hsub hz)) (fun z hz => hβrel z (hsub hz))
    hz₀front hβan hβmod ?_
  -- non-criticality: an `EqOn` on the ball's basin part is a `𝓝[K₁ᶜ]`-germ equality
  intro k hEqOn
  have hmem : V ∩ (filledJulia c₁)ᶜ ∈ 𝓝[(filledJulia c₁)ᶜ] z₀ :=
    Filter.inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hρpos)) self_mem_nhdsWithin
  exact hnoncrit k (Filter.eventually_of_mem hmem (fun z hz => hEqOn hz))

end Bottcher
