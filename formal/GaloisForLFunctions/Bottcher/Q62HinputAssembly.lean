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
import GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary

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

/-- **`hinput` middle.**  Relocate a separable-fibre witness onto the frontier and produce the
natural-boundary tuple.  Given the fibre coefficients analytic on the basin and across the frontier, a
separable-fibre witness `wfar` in the basin, β a root on the basin, and the isolated topological input
that the *locally connected* frontier points are uncountable, some frontier point carries a separable
fibre and the boundary limit `Tendsto β (𝓝[K₁ᶜ] z₀) (𝓝 w₀)`. -/
theorem hinput_tuple_of_relation
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c : ℂ} {β : ℂ → ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha_basin : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c)ᶜ)
    (ha_front : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (frontier (filledJulia c)))
    {wfar : ℂ} (hwfar : wfar ∈ (filledJulia c)ᶜ) (hleadfar : a N wfar ≠ 0)
    (hsepfar : (fibrePoly a s wfar).Separable)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβrel : ∀ z ∈ (filledJulia c)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hunc : ¬ ({z ∈ frontier (filledJulia c) |
        ∀ ρ : ℝ, 0 < ρ → ∃ U : Set ℂ, U ⊆ Metric.ball z ρ ∧ U ⊆ (filledJulia c)ᶜ ∧
          IsPreconnected U ∧ U ∈ 𝓝[(filledJulia c)ᶜ] z}).Countable) :
    ∃ z₀ w₀ : ℂ, (fibrePoly a s z₀).Separable ∧ z₀ ∈ frontier (filledJulia c) ∧
      Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀) := by
  set Ω : Set ℂ := (filledJulia c)ᶜ ∪ frontier (filledJulia c) with hΩdef
  have hΩsub : Ω ⊆ closure ((filledJulia c)ᶜ) := by
    intro z hz
    rcases hz with h | h
    · exact subset_closure h
    · exact frontier_subset_closure (by rwa [frontier_compl])
  have hΩc : IsPreconnected Ω :=
    (isPreconnected_compl_filledJulia c).subset_closure subset_union_left hΩsub
  have ha_Ω : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω := by
    intro i hi z hz
    rcases hz with h | h
    · exact ha_basin i hi z h
    · exact ha_front i hi z h
  set S : Set ℂ := {z ∈ frontier (filledJulia c) |
      ∀ ρ : ℝ, 0 < ρ → ∃ U : Set ℂ, U ⊆ Metric.ball z ρ ∧ U ⊆ (filledJulia c)ᶜ ∧
        IsPreconnected U ∧ U ∈ 𝓝[(filledJulia c)ᶜ] z} with hSdef
  have hSsubΩ : S ⊆ Ω := fun z hz => Or.inr hz.1
  have hunc' : ¬ (S ∩ Ω).Countable := by
    rwa [Set.inter_eq_self_of_subset_left hSsubΩ]
  obtain ⟨z₀, hz₀S, hlead_z₀, hsep_z₀⟩ :=
    exists_sparse_fibre_separable_uncountable hN1 hsupp hN hΩc ha_Ω (Or.inl hwfar)
      hleadfar hsepfar hunc'
  have hz₀front : z₀ ∈ frontier (filledJulia c) := hz₀S.1
  have ha_z₀ : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀ :=
    fun i hi => (ha_front i hi z₀ hz₀front).contDiffAt
  obtain ⟨w₀, hsep', _, htend⟩ :=
    hinput_tuple_of_basin_locally_connected hsupp hN hN1 ha_z₀ hlead_z₀ hsep_z₀ hz₀front
      hβan hβrel hz₀S.2
  exact ⟨z₀, w₀, hsep', hz₀front, htend⟩

/-- **`hinput` wiring.**  Instantiates the middle producer with the engine's continued coefficients
`a i = (Q i)(γ)`, deriving analyticity across the frontier and `β`-a-root-on-the-basin from the engine's
hypotheses (the engine's own `hβrel_all` derivation).  Produces the exact `hinput` tuple for one
relation carrying a separable-fibre witness. -/
theorem hinput_tuple_of_engine_relation
    {U : Set ℂ} {c₁ c₂ : ℂ} {β γ : ℂ → ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hU₁ : U ⊆ escapeOpen c₁)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Q : ℕ → Polynomial (Polynomial ℂ)} {s : Finset ℕ} {N : ℕ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {wfar : ℂ} (hwfar : wfar ∈ (filledJulia c₁)ᶜ)
    (hleadfar : (Q N).eval₂ (Polynomial.evalRingHom wfar) (γ wfar) ≠ 0)
    (hsepfar : (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s wfar).Separable)
    (hunc : ¬ ({z ∈ frontier (filledJulia c₁) |
        ∀ ρ : ℝ, 0 < ρ → ∃ V : Set ℂ, V ⊆ Metric.ball z ρ ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          IsPreconnected V ∧ V ∈ 𝓝[(filledJulia c₁)ᶜ] z}).Countable) :
    ∃ z₀ w₀ : ℂ,
      (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
      z₀ ∈ frontier (filledJulia c₁) ∧
      Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) := by
  set a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z) with hadef
  have ha_basin : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ :=
    fun i _ => analyticOnNhd_eval₂_of_analyticOnNhd hγan (Q i)
  have ha_front : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (frontier (filledJulia c₁)) :=
    fun i _ => analyticOnNhd_eval₂_of_analyticOnNhd hγfront (Q i)
  have hUbasin : U ⊆ (filledJulia c₁)ᶜ := fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)
  have hmatch : ∀ i ∈ s, ∀ z ∈ U,
      a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
    intro i _ z hz
    show (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
        = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)
    rw [hγmatch z hz]
  have hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    calc ∑ i ∈ s, a i z * (β z) ^ i
        = ∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
      _ = 0 := hEqOn hz
  have hβrel : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    relation_eq_zero_basin_analytic_of_open hUo hUne hUbasin ha_basin hβan hrelU
  exact hinput_tuple_of_relation hsupp hN hN1 ha_basin ha_front hwfar hleadfar hsepfar hβan hβrel hunc

/-- The isolated **topological input** for the natural-boundary `hinput`: the frontier points at which
the basin has a local basis of preconnected neighbourhoods form an uncountable set (co-countable for
connected `c`: countable branch points for dendrites; a quasicircle for hyperbolic parameters). -/
def UncountableLocallyConnectedFrontier (c : ℂ) : Prop :=
  ¬ ({z ∈ frontier (filledJulia c) |
      ∀ ρ : ℝ, 0 < ρ → ∃ V : Set ℂ, V ⊆ Metric.ball z ρ ∧ V ⊆ (filledJulia c)ᶜ ∧
        IsPreconnected V ∧ V ∈ 𝓝[(filledJulia c)ᶜ] z}).Countable

/-- **The natural-boundary `hinput`, as a theorem.**  The producer the engine
`noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable` consumes, discharged from the
scaffold and reduced to exactly two isolated inputs: the topological `UncountableLocallyConnectedFrontier`
(one-sidedness, co-countable for connected `c₁`) and a per-relation separable-fibre witness in the basin
(the squarefree / minimal-relation content).  Everything else is assembled from proven lemmas. -/
theorem hinput_of_witness_of_uncountableLC
    {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    {c₁ c₂ : ℂ} {β γ : ℂ → ℂ} {hU₂ : U ⊆ escapeOpen c₂}
    (hU₁ : U ⊆ escapeOpen c₁)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hunc : UncountableLocallyConnectedFrontier c₁)
    (hwitness : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (wfar : ℂ), s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          wfar ∈ (filledJulia c₁)ᶜ ∧
          (Q N).eval₂ (Polynomial.evalRingHom wfar) (γ wfar) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s wfar).Separable) :
    ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) := by
  intro Q s hnt hEqOn
  obtain ⟨N, wfar, hsupp, hN, hN1, hwfar, hlead, hsep⟩ := hwitness Q s hnt hEqOn
  exact hinput_tuple_of_engine_relation hUo hUne hU₁ hβan hβesc hγan hγfront hγmatch
    hsupp hN hN1 hEqOn hwfar hlead hsep hunc

end Bottcher
