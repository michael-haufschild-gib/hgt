/-
# The smooth-piece reflection discharge, from the branch relation

The final bridge of the harmonic Schwarz-reflection route to the both-connected smooth-piece rigidity
(P6, #118).  `continuesAcross_of_basinBranch` (`BottcherArcExtension.lean`) reduced the whole reflection
stack to a single input: the arc branch `φ` *equals the Böttcher branch* `β` on the basin side of a
neighbourhood of the frontier point.  This file supplies exactly that from the fibre relation.

`β` is a root of the fibre polynomial on the basin (the bivariate relation being refuted, propagated
across the whole basin by the identity theorem), and the `wfam` branches are its *complete* separated
root family, so `eqOn_branch_of_relation_analytic` identifies `β = wfam k` on any preconnected basin
neighbourhood.  That is the basin-branch datum: `continuesAcross_of_basinBranch` then produces the
analytic continuation of `β` across the frontier point, contradicting the natural boundary.

The remaining inputs are the ones the whole #118 chain shares — a **preconnected basin neighbourhood**
at the frontier point (basin one-sidedness / local connectivity, co-countable for connected `c₁`) and
that the matched branch is a **non-critical** local biholomorphism at the arc point (`deriv ≠ 0`,
`‖·‖ = 1`) — plus the fibre relation, all threaded through here.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import GaloisForLFunctions.Bottcher.BottcherArcExtension
import GaloisForLFunctions.Bottcher.RelativeBranchFamily

open Set Filter Topology Complex

namespace Bottcher

/-- **Böttcher continuation across the smooth piece, from the fibre relation.**  On a preconnected
basin neighbourhood `V ∩ K₁ᶜ` where the fibre polynomial has constant degree `N` with the complete
separated continuous root family `wfam` and `β` satisfies the fibre relation, `β` coincides with one
branch `wfam k` (`eqOn_branch_of_relation_analytic`).  If that matched branch is a non-critical local
biholomorphism at the frontier point `z₀` (`AnalyticAt`, `deriv ≠ 0`, `‖wfam k z₀‖ = 1`), the harmonic
reflection (`continuesAcross_of_basinBranch`) continues `β` analytically across `z₀`.  This is the
smooth-piece boundary discharge of the both-connected gatekeeper via the harmonic route — the
continuation is *constructed*, not assumed. -/
theorem continuesAcross_of_smoothBranch
    {c₁ : ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {wfam : Fin N → ℂ → ℂ}
    {β : ℂ → ℂ} {z₀ : ℂ} {V : Set ℂ}
    (hN1 : 1 ≤ N) (hVo : IsOpen V) (hz₀V : z₀ ∈ V)
    (hUconn : IsPreconnected (V ∩ (filledJulia c₁)ᶜ))
    (hUne : (V ∩ (filledJulia c₁)ᶜ).Nonempty)
    (hwc : ∀ k, ContinuousOn (wfam k) (V ∩ (filledJulia c₁)ᶜ))
    (hβc : ContinuousOn β (V ∩ (filledJulia c₁)ᶜ))
    (hsep : ∀ z ∈ V ∩ (filledJulia c₁)ᶜ, ∀ k l, k ≠ l → wfam k z ≠ wfam l z)
    (hdeg : ∀ z ∈ V ∩ (filledJulia c₁)ᶜ, (fibrePoly a s z).natDegree = N)
    (hwroot : ∀ k, ∀ z ∈ V ∩ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (wfam k z) ^ i = 0)
    (hβrel : ∀ z ∈ V ∩ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hz₀front : z₀ ∈ frontier (filledJulia c₁))
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hnoncrit : ∀ k, Set.EqOn β (wfam k) (V ∩ (filledJulia c₁)ᶜ) →
        AnalyticAt ℂ (wfam k) z₀ ∧ deriv (wfam k) z₀ ≠ 0 ∧ ‖wfam k z₀‖ = 1) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  obtain ⟨z₁, hz₁⟩ := hUne
  obtain ⟨k, hβwk⟩ :=
    eqOn_branch_of_relation_analytic hN1 wfam β hUconn hwc hβc hsep hdeg hwroot hβrel hz₁
  obtain ⟨hφAt, hd0, hmod⟩ := hnoncrit k hβwk
  have hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ (filledJulia c₁)ᶜ → wfam k z = β z := by
    filter_upwards [hVo.mem_nhds hz₀V] with z hzV hzKc
    exact (hβwk ⟨hzV, hzKc⟩).symm
  exact continuesAcross_of_basinBranch hφAt hd0 hmod hz₀front hgβ hβan hβmod

end Bottcher
