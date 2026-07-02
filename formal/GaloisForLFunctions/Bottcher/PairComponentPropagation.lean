/-
# Relation propagation to the tip through the unbounded component (P5, propagation half)

The bivariate relation between two connected-parameter Böttcher branches, assumed on a far-field
set `U`, holds at **every** point carrying an unbounded preconnected escape set in the joint
complement — exactly the points the hole-free tip supplies.  The mechanism: the escape set, the
far-field annulus `escapeOpen c₁ ∩ escapeOpen c₂` (one of the two escape sets, whichever is
smaller), and `U` all lie in one connected component `Ω` of the open joint complement; both global
basin branches are analytic on `Ω`; the identity theorem propagates the vanishing from `U` to `Ω`.

Combined with the root-limit lemma this yields the **modulus-one supply**: every Julia point of
the tip ball carries a modulus-one root of its limiting fibre polynomial.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.TipWApproach
import GaloisForLFunctions.Bottcher.RootLimitModulus
import GaloisForLFunctions.Bottcher.TranscendenceReduction
import GaloisForLFunctions.Bottcher.BasinConnected
import GaloisForLFunctions.Bottcher.GlobalBasinBranch

open Polynomial Set Metric Bornology Filter Topology

namespace Bottcher

/-- The joint far field is one of the two escape annuli (the one with the larger radius), hence
preconnected and nonempty. -/
theorem isConnected_escapeOpen_inter (c₁ c₂ : ℂ) :
    IsConnected (escapeOpen c₁ ∩ escapeOpen c₂) := by
  rcases le_total (max 2 ‖c₁‖) (max 2 ‖c₂‖) with h | h
  · have heq : escapeOpen c₁ ∩ escapeOpen c₂ = escapeOpen c₂ := by
      apply Set.inter_eq_self_of_subset_right
      intro z hz
      exact lt_of_le_of_lt h hz
    rw [heq]
    exact isConnected_escapeOpen c₂
  · have heq : escapeOpen c₁ ∩ escapeOpen c₂ = escapeOpen c₁ := by
      apply Set.inter_eq_self_of_subset_left
      intro z hz
      exact lt_of_le_of_lt h hz
    rw [heq]
    exact isConnected_escapeOpen c₁

/-- **Relation propagation to an escape-carrying point.**  If the cleared bivariate relation
vanishes on a far-field set `U`, then it holds — evaluated through the global basin branches
`β₁, β₂` — at every point `q` of the joint complement that carries an unbounded preconnected
escape set `V`.  Identity theorem on the connected component of `q`. -/
theorem pair_relation_at_escape_point {c₁ c₂ : ℂ}
    {β₁ β₂ : ℂ → ℂ}
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {q : ℂ} {V : Set ℂ} (hqV : q ∈ V) (hVc : IsPreconnected V) (hVunbd : ¬ IsBounded V)
    (hVsub : V ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ) :
    ∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom q) (β₂ q)) * (β₁ q) ^ i = 0 := by
  classical
  -- the open joint complement and the component of `q`
  set D : Set ℂ := (filledJulia c₁ ∪ filledJulia c₂)ᶜ with hDdef
  have hDo : IsOpen D :=
    ((isClosed_filledJulia c₁).union (isClosed_filledJulia c₂)).isOpen_compl
  set Ω : Set ℂ := connectedComponentIn D q with hΩdef
  have hΩo : IsOpen Ω := hDo.connectedComponentIn
  have hΩc : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hΩsub : Ω ⊆ D := connectedComponentIn_subset D q
  have hqΩ : q ∈ Ω := mem_connectedComponentIn (hVsub hqV)
  have hVΩ : V ⊆ Ω := hVc.subset_connectedComponentIn hqV hVsub
  -- the joint far field sits in the same component
  set E : Set ℂ := escapeOpen c₁ ∩ escapeOpen c₂ with hEdef
  have hEc : IsConnected E := isConnected_escapeOpen_inter c₁ c₂
  have hED : E ⊆ D := by
    intro z hz
    rintro (h | h)
    · exact escapeOpen_subset_compl_filledJulia c₁ hz.1 h
    · exact escapeOpen_subset_compl_filledJulia c₂ hz.2 h
  obtain ⟨v, hvV, hvE⟩ : ∃ v ∈ V, v ∈ E := by
    rw [isBounded_iff_forall_norm_le] at hVunbd
    push Not at hVunbd
    obtain ⟨v, hvV, hv⟩ := hVunbd (max (max 2 ‖c₁‖) (max 2 ‖c₂‖))
    exact ⟨v, hvV, lt_of_le_of_lt (le_max_left _ _) hv,
      lt_of_le_of_lt (le_max_right _ _) hv⟩
  have hEΩ : E ⊆ Ω := by
    have hvΩ : v ∈ Ω := hVΩ hvV
    rw [hΩdef, connectedComponentIn_eq hvΩ]
    exact hEc.isPreconnected.subset_connectedComponentIn hvE hED
  have hUΩ : U ⊆ Ω := fun z hz => hEΩ ⟨hU₁ hz, hU₂ hz⟩
  -- the relation function through the basin branches, analytic on the component
  set F : ℂ → ℂ := fun z => ∑ i ∈ s,
      ((Q i).eval₂ (Polynomial.evalRingHom z) (β₂ z)) * (β₁ z) ^ i with hFdef
  have hβ₁Ω : AnalyticOnNhd ℂ β₁ Ω := hβ₁an.mono fun z hz h => (hΩsub hz) (Or.inl h)
  have hβ₂Ω : AnalyticOnNhd ℂ β₂ Ω := hβ₂an.mono fun z hz h => (hΩsub hz) (Or.inr h)
  have hFan : AnalyticOnNhd ℂ F Ω := by
    apply Finset.analyticOnNhd_fun_sum
    intro i _hi
    exact (analyticOnNhd_eval₂_of_analyticOnNhd hβ₂Ω (Q i)).mul (hβ₁Ω.pow i)
  -- vanishing near a point of `U`
  obtain ⟨w₀, hw₀U⟩ := hUne
  have hloc : ∀ᶠ z in 𝓝 w₀, F z = 0 := by
    filter_upwards [hUo.mem_nhds hw₀U] with z hzU
    have h1 := hEqOn hzU
    simp only [Pi.zero_apply] at h1
    rw [hFdef]
    simp only
    calc ∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (β₂ z)) * (β₁ z) ^ i
        = ∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hβ₁esc z (hU₁ hzU), hβ₂esc z (hU₂ hzU)]
      _ = 0 := h1
  -- identity theorem on the component
  have hEqΩ : Set.EqOn F 0 Ω := by
    have hev : F =ᶠ[𝓝 w₀] (fun _ => (0 : ℂ)) := by
      filter_upwards [hloc] with z hz using hz
    exact hFan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩc
      (hUΩ hw₀U) hev
  exact hEqΩ hqΩ

/-- **Modulus-one supply at every Julia point of the tip ball.**  Under a hole-free tip and the
far-field relation, every `w ∈ J₁ ∩ B(z₀, r)` carries a modulus-one root of the limiting fibre
polynomial with coefficients `a_i(w) = Q_i(w, β₂(w))`.  This is the input of the Baire pigeonhole:
the approach points come from `holeFreeTip_frontier_approach`, their relation values from
`pair_relation_at_escape_point`, and the limit from the root-limit lemma. -/
theorem holeFreeTip_modulus_one_supply {c₁ c₂ : ℂ}
    {β₁ β₂ : ℂ → ℂ}
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {z₀ : ℂ} {r : ℝ} (htip : HoleFreeTip c₁ c₂ z₀ r)
    {w : ℂ} (hw : w ∈ frontier (filledJulia c₁)) (hwball : w ∈ Metric.ball z₀ r) :
    ∃ x : ℂ, ‖x‖ = 1 ∧
      ∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom w) (β₂ w)) * x ^ i = 0 := by
  classical
  -- the approach sequence from the hole-free tip
  have happrox := holeFreeTip_frontier_approach htip hw hwball
  have hchoice : ∀ k : ℕ, ∃ q, q ∈ Metric.ball w (1 / (k + 1)) ∧ q ∈ Metric.ball z₀ r ∧
      q ∉ filledJulia c₁ ∧ ∃ V : Set ℂ, q ∈ V ∧ IsPreconnected V ∧ ¬ IsBounded V ∧
        V ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ := by
    intro k
    exact happrox (1 / (k + 1)) (by positivity)
  choose z hz1 hz2 hz3 V hV1 hV2 hV3 hV4 using hchoice
  -- convergence of the approach sequence
  have hztend : Tendsto z atTop (𝓝 w) := by
    have hd : ∀ k : ℕ, dist (z k) w ≤ 1 / ((k : ℝ) + 1) := fun k =>
      (Metric.mem_ball.mp (hz1 k)).le
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg) hd tendsto_one_div_add_atTop_nhds_zero_nat
  -- the coefficients, continuous at `w` (the ball is K₂-free)
  set a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (β₂ z) with hadef
  have hwK₂ : w ∈ (filledJulia c₂)ᶜ := by
    intro hmem
    have : w ∈ Metric.ball z₀ r ∩ filledJulia c₂ := ⟨hwball, hmem⟩
    rw [htip.2.2.1] at this
    exact this
  have hcont : ∀ i ∈ s, ContinuousAt (a i) w := by
    intro i _hi
    have h1 : AnalyticOnNhd ℂ (a i) (filledJulia c₂)ᶜ :=
      analyticOnNhd_eval₂_of_analyticOnNhd hβ₂an (Q i)
    exact (h1 w hwK₂).continuousAt
  -- roots with the genuine Böttcher modulus along the sequence
  have hroot : ∀ k, ∑ i ∈ s, a i (z k) * (β₁ (z k)) ^ i = 0 := by
    intro k
    exact pair_relation_at_escape_point hβ₁an hβ₁esc hβ₂an hβ₂esc hUo hUne hU₁ hU₂ Q s
      hEqOn (hV1 k) (hV2 k) (hV3 k) (hV4 k)
  have hmod : ∀ k, ‖β₁ (z k)‖ = Real.exp (greenFunctionDyn c₁ (z k)) := by
    intro k
    exact hβ₁mod (z k) (hz3 k)
  have hwK₁ : w ∈ filledJulia c₁ := (isClosed_filledJulia c₁).frontier_subset hw
  exact exists_modulus_one_root_of_root_limit_green hwK₁ hztend hcont hroot hmod

end Bottcher
