/-
# One-sidedness pulls back along the backward dynamics (the squaring engine for #133)

The RHTower lane's diagnosis (logs/rhtower-to-q62-transfer.md): the modulus `|·|` is
reflection-symmetric, hence orientation-blind, so the one-sidedness / arc-orientation residual of
`OneSidedDense` (#133) cannot come from the potential — it must come from the **dynamics** (the
squaring `β(z²+c) = β(z)²`).  This file supplies that engine.

`LocOneSided c z` is the homeomorphism-robust (neighbourhood-basis) form of one-sidedness: `z` on the
Julia frontier with arbitrarily small open neighbourhoods whose **basin part `V ∩ K^c` is
preconnected**.  The main theorem `locOneSided_of_quadratic_preimage` transports it along the backward
dynamics: if `q z` is `LocOneSided` and `q = z²+c` is a local biholomorphism at `z` (i.e. `z ≠ 0`, the
only critical point), then `z` is `LocOneSided`.  Engine: the filled set is `q`-invariant
(`mem_filledJulia_iff_quadratic_mem`), so the local inverse `γ = q⁻¹` (`exists_localInverse_of_
continuation`, `deriv q z = 2z ≠ 0`) carries the small preconnected basin neighbourhood of `q z` back to
one at `z` — `V ∩ K^c = γ '' (V' ∩ K^c)`, preconnected as a continuous image.

Consequences: `locOneSided_of_oneSidedAt` (the tree's ball-`OneSidedAt` gives `LocOneSided`) and
`exists_preconnected_basin_nhd_of_locOneSided` (feeds the branch-route input of
`continuesAcross_of_smoothBranch`).  Since preimages of a frontier point under `q` are dense in the
Julia set, ONE `LocOneSided` point spreads (via its backward orbit) to a dense set — the
pullback-density route to `OneSidedDense` that needs no prime-end theory.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.OneSidedCertificate
import GaloisForLFunctions.Bottcher.InteriorModulusObstruction
import GaloisForLFunctions.Bottcher.JuliaFrontierPreimage

open Set Metric Filter Topology Complex

namespace Bottcher

/-- **Neighbourhood-basis one-sidedness** — the homeomorphism-robust form.  `z` is a Julia frontier
point with arbitrarily small open neighbourhoods `V` whose basin part `V ∩ (filledJulia c)ᶜ` is
preconnected and nonempty.  Unlike the metric-ball `OneSidedAt`, this form is preserved by local
biholomorphisms, so it transports along the dynamics. -/
def LocOneSided (c z : ℂ) : Prop :=
  z ∈ frontier (filledJulia c) ∧
    ∀ ε > 0, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Metric.ball z ε ∧
      IsPreconnected (V ∩ (filledJulia c)ᶜ) ∧ (V ∩ (filledJulia c)ᶜ).Nonempty

/-- **Ball one-sidedness ⟹ neighbourhood-basis one-sidedness.**  Metric balls are a neighbourhood
basis, and `ball z ρ \ K = ball z ρ ∩ Kᶜ`, so the tree's `OneSidedAt` gives `LocOneSided`. -/
theorem locOneSided_of_oneSidedAt {c z : ℂ} (h : OneSidedAt c z) : LocOneSided c z := by
  obtain ⟨hzf, ρ₀, hρ₀, hconn⟩ := h
  refine ⟨hzf, fun ε hε => ⟨Metric.ball z (min ρ₀ ε), Metric.isOpen_ball,
    Metric.mem_ball_self (lt_min hρ₀ hε), Metric.ball_subset_ball (min_le_right _ _), ?_, ?_⟩⟩
  · have hc := hconn (min ρ₀ ε) (lt_min hρ₀ hε) (min_le_left _ _)
    rw [Set.sdiff_eq] at hc; exact hc.isPreconnected
  · have hc := hconn (min ρ₀ ε) (lt_min hρ₀ hε) (min_le_left _ _)
    rw [Set.sdiff_eq] at hc; exact hc.nonempty

/-- **`LocOneSided` feeds the branch route.**  It yields the open preconnected basin neighbourhood
`continuesAcross_of_smoothBranch` consumes. -/
theorem exists_preconnected_basin_nhd_of_locOneSided {c z : ℂ} (h : LocOneSided c z) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ IsPreconnected (V ∩ (filledJulia c)ᶜ) ∧
      (V ∩ (filledJulia c)ᶜ).Nonempty := by
  obtain ⟨_, hbasis⟩ := h
  obtain ⟨V, hVo, hzV, _, hVpre, hVne⟩ := hbasis 1 one_pos
  exact ⟨V, hVo, hzV, hVpre, hVne⟩

/-- **One-sidedness pulls back along the backward dynamics.**  If `q z` (`q = z²+c`) is `LocOneSided`
and `z ≠ 0` (so `q` is a local biholomorphism at `z`, `deriv q z = 2z ≠ 0`), then `z` is `LocOneSided`.
The filled Julia set is `q`-invariant, so the local inverse `γ` carries any small preconnected basin
neighbourhood `V'` of `q z` back to `V ∩ Kᶜ = γ '' (V' ∩ Kᶜ)` at `z`, preconnected as a continuous
image.  This is the squaring-powered engine: the orientation the modulus cannot see is supplied by the
dynamics. -/
theorem locOneSided_of_quadratic_preimage {c z : ℂ} (hz0 : z ≠ 0)
    (hzf : z ∈ frontier (filledJulia c))
    (hz' : LocOneSided c (quadratic c z)) :
    LocOneSided c z := by
  refine ⟨hzf, ?_⟩
  obtain ⟨_hz'f, hbasis⟩ := hz'
  -- `q` is a local biholomorphism at `z`
  have hqAn : AnalyticAt ℂ (quadratic c) z := (analyticAt_id.pow 2).add analyticAt_const
  have hqd : HasDerivAt (quadratic c) (2 * z) z := by
    have hpow : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
    exact hpow.add_const c
  have hd0 : deriv (quadratic c) z ≠ 0 := by rw [hqd.deriv]; exact mul_ne_zero two_ne_zero hz0
  obtain ⟨γ, hγAn, hγleft, hγright⟩ := exists_localInverse_of_continuation hqAn hd0
  have hγz : γ (quadratic c z) = z := hγleft.self_of_nhds
  have hqcont : Continuous (quadratic c) := (continuous_pow 2).add continuous_const
  have hKcinv : ∀ w, w ∈ (filledJulia c)ᶜ ↔ quadratic c w ∈ (filledJulia c)ᶜ := fun w => by
    rw [Set.mem_compl_iff, Set.mem_compl_iff, mem_filledJulia_iff_quadratic_mem]
  intro ε hε
  -- the ball `B ∋ z` inside `ball z ε` on which `γ ∘ q = id`
  obtain ⟨ρ, hρ, hballz⟩ := Metric.eventually_nhds_iff.mp hγleft
  set B : Set ℂ := Metric.ball z (min ρ ε) with hBdef
  have hBinv : ∀ w ∈ B, γ (quadratic c w) = w := fun w hw =>
    hballz (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
  have hBε : B ⊆ Metric.ball z ε := Metric.ball_subset_ball (min_le_right _ _)
  -- the region `ball (q z) δ` where `q ∘ γ = id`, `γ` is analytic, and `γ` lands in `B`
  have hγtend : Tendsto γ (𝓝 (quadratic c z)) (𝓝 z) := by
    have h := hγAn.continuousAt.tendsto; rwa [hγz] at h
  obtain ⟨δ, hδ, hballw⟩ := Metric.eventually_nhds_iff.mp
    (hγright.and (hγAn.eventually_analyticAt.and
      (hγtend (Metric.ball_mem_nhds z (lt_min hρ hε)))))
  -- pull back a small preconnected basin neighbourhood of `q z`
  obtain ⟨V', hV'o, hz'V', hV'ball, hV'pre, hV'ne⟩ := hbasis δ hδ
  set V : Set ℂ := (quadratic c) ⁻¹' V' ∩ B with hVdef
  have hzV : z ∈ V := ⟨hz'V', Metric.mem_ball_self (lt_min hρ hε)⟩
  -- the key identity `V ∩ Kᶜ = γ '' (V' ∩ Kᶜ)`
  have hVKc : V ∩ (filledJulia c)ᶜ = γ '' (V' ∩ (filledJulia c)ᶜ) := by
    apply Set.eq_of_subset_of_subset
    · rintro w ⟨⟨hwV', hwB⟩, hwKc⟩
      exact ⟨quadratic c w, ⟨hwV', (hKcinv w).mp hwKc⟩, hBinv w hwB⟩
    · rintro _ ⟨v, ⟨hvV', hvKc⟩, rfl⟩
      obtain ⟨hqγ, _, hγvB⟩ := hballw (Metric.mem_ball.mp (hV'ball hvV'))
      exact ⟨⟨by rw [Set.mem_preimage, hqγ]; exact hvV', hγvB⟩, by rw [hKcinv, hqγ]; exact hvKc⟩
  have hγcont : ContinuousOn γ (V' ∩ (filledJulia c)ᶜ) := fun v hv =>
    ((hballw (Metric.mem_ball.mp (hV'ball hv.1))).2.1).continuousAt.continuousWithinAt
  exact ⟨V, (hV'o.preimage hqcont).inter Metric.isOpen_ball, hzV,
    (Set.inter_subset_right).trans hBε, by rw [hVKc]; exact hV'pre.image γ hγcont,
    by rw [hVKc]; exact hV'ne.image γ⟩

/-- **Iterated pullback.**  If `z₀` is `LocOneSided` and `z` is an `n`-fold `q`-preimage of `z₀`
(`q^[n] z = z₀`) whose forward orbit `z, q z, …, q^{n-1} z` avoids the critical point `0`, then `z` is
`LocOneSided`.  Iterating `locOneSided_of_quadratic_preimage`; each preimage stays on the Julia frontier
by `quadratic_mem_frontier_iff`. -/
theorem locOneSided_iterate_preimage {c z₀ : ℂ} (hz₀ : LocOneSided c z₀) :
    ∀ (n : ℕ) (z : ℂ), (quadratic c)^[n] z = z₀ → (∀ i < n, (quadratic c)^[i] z ≠ 0) →
      LocOneSided c z := by
  intro n
  induction n with
  | zero =>
    intro z hz _
    rw [Function.iterate_zero_apply] at hz
    rw [hz]; exact hz₀
  | succ k ih =>
    intro z hz hne
    have hqz : (quadratic c)^[k] (quadratic c z) = z₀ := by
      rw [← Function.iterate_succ_apply]; exact hz
    have hqne : ∀ i < k, (quadratic c)^[i] (quadratic c z) ≠ 0 := fun i hi => by
      rw [← Function.iterate_succ_apply]; exact hne (i + 1) (by omega)
    have hqzLoc : LocOneSided c (quadratic c z) := ih (quadratic c z) hqz hqne
    have hz0 : z ≠ 0 := by
      have := hne 0 (Nat.zero_lt_succ k); rwa [Function.iterate_zero_apply] at this
    exact locOneSided_of_quadratic_preimage hz0 (quadratic_mem_frontier_iff.mp hqzLoc.1) hqzLoc

/-- **Backward-orbit density** (the classical dynamical input, isolated as a named Prop).  Near every
Julia frontier point there is a non-critical `q`-preimage of the base point `z₀` — i.e. the backward
orbit of `z₀`, avoiding the critical orbit, is dense in the frontier.  For `z²+c` this is Brolin's
theorem (preimages equidistribute to the equilibrium measure, whose support is the Julia set); it is
mathlib-absent, and the tree's `Bottcher/Brolin/` Riesz-measure stack is its natural home. -/
def BackwardOrbitDense (c z₀ : ℂ) : Prop :=
  ∀ p ∈ frontier (filledJulia c), ∀ ε > 0, ∃ (n : ℕ) (z : ℂ),
    (quadratic c)^[n] z = z₀ ∧ (∀ i < n, (quadratic c)^[i] z ≠ 0) ∧ dist p z < ε

/-- **Density of `LocOneSided` points.**  `LocOneSided` points are dense in the Julia frontier — the
form the both-connected branch route (`continuesAcross_of_smoothBranch`) consumes at its non-critical
piece point. -/
def LocOneSidedDense (c : ℂ) : Prop :=
  ∀ p ∈ frontier (filledJulia c), ∀ ε > 0, ∃ z, LocOneSided c z ∧ dist p z < ε

/-- **The pullback-density route to one-sidedness density.**  From ONE `LocOneSided` base point `z₀` and
the backward-orbit density of `z₀`, `LocOneSided` points are dense in the frontier: each dense
non-critical preimage of `z₀` is `LocOneSided` by the iterated pullback.  This reduces the one-sidedness
density that the both-connected endgame needs to exactly two classical inputs — a base one-sided point and
Brolin backward-orbit density — with **no prime-end / ray-landing theory**. -/
theorem locOneSidedDense_of_base_backwardDense {c z₀ : ℂ}
    (hbase : LocOneSided c z₀) (hbwd : BackwardOrbitDense c z₀) :
    LocOneSidedDense c := by
  intro p hp ε hε
  obtain ⟨n, z, hzn, hzne, hdist⟩ := hbwd p hp ε hε
  exact ⟨z, locOneSided_iterate_preimage hbase n z hzn hzne, hdist⟩

end Bottcher
