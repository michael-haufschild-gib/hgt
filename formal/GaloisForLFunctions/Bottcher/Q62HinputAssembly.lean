/-
# Assembling the natural-boundary `hinput` producer

The natural-boundary engine `noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable`
(RelativeRigidityNaturalBoundary.lean) consumes one hypothesis `hinput`: for a candidate relation, a
frontier point `z₀` with separable continued fibre together with a boundary limit
`Tendsto β (𝓝[K₁ᶜ] z₀) (𝓝 w₀)`.  This file assembles that producer from already-proven pieces:

* `exists_branch_family_analytic` — the IFT root branches at a separable point;
* `relation_eq_zero_basin_analytic_of_open` — β is a root of the fibre on the whole basin (identity theorem);
* `dendrite_branch_limit_analytic` — the boundary limit from a preconnected basin neighbourhood;
* `exists_sparse_fibre_separable_countableAvoidance` — relocate a separable-fibre witness onto the frontier.

The assembly is unconditional **except** for one isolated topological input: a local basis of
preconnected basin neighbourhoods at the frontier point (basin local connectivity / one-sidedness).
This is the genuine remaining content of the natural-boundary route (co-countable for connected `c₁`:
countable branch points for dendrites, a quasicircle for hyperbolic parameters).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.Bottcher.RelativeDenseApproach
import GaloisForLFunctions.Bottcher.BasinColimit
import GaloisForLFunctions.Bottcher.RelativeFibreGeneric
import GaloisForLFunctions.Bottcher.FilledJuliaConnected

open Polynomial Filter Topology Set Metric

namespace Bottcher

/-- **`hinput` back-half.**  At a frontier point `z₀` with separable continued fibre, β a root of the
fibre on the whole basin, and a local basis of preconnected basin neighbourhoods at `z₀`, produce the
natural-boundary tuple: separable fibre at `z₀`, `z₀` on the frontier, and a boundary limit
`Tendsto β (𝓝[K₁ᶜ] z₀) (𝓝 w₀)`. -/
theorem hinput_tuple_of_basin_locally_connected
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ} {β : ℂ → ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha_z₀ : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    (hz₀front : z₀ ∈ frontier (filledJulia c))
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβrel : ∀ z ∈ (filledJulia c)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hlc : ∀ ρ : ℝ, 0 < ρ → ∃ U : Set ℂ, U ⊆ Metric.ball z₀ ρ ∧ U ⊆ (filledJulia c)ᶜ ∧
        IsPreconnected U ∧ U ∈ 𝓝[(filledJulia c)ᶜ] z₀) :
    ∃ w₀ : ℂ, (fibrePoly a s z₀).Separable ∧ z₀ ∈ frontier (filledJulia c) ∧
      Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀) := by
  obtain ⟨rBr, w, hrBr, hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha_z₀ hlead hsep
  obtain ⟨U, hUball, hUbasin, hUpre, hUnhds⟩ := hlc rBr hrBr
  have hz₀cl : z₀ ∈ closure ((filledJulia c)ᶜ) :=
    frontier_subset_closure (by rwa [frontier_compl])
  have hne : (𝓝[(filledJulia c)ᶜ] z₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz₀cl
  obtain ⟨z₁, hz₁⟩ := hne.nonempty_of_mem hUnhds
  have hβc : ContinuousOn β U := hβan.continuousOn.mono hUbasin
  have hβrel_U : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := fun z hz => hβrel z (hUbasin hz)
  obtain ⟨w₀, d, hroot, hpart, hd, htend⟩ :=
    dendrite_branch_limit_analytic hN1 hrBr hsep w hwc hwsep hwdeg hwrel
      hUball hUbasin hUpre hUnhds hβc hβrel_U hz₁
  exact ⟨w₀, hsep, hz₀front, htend⟩

end Bottcher
