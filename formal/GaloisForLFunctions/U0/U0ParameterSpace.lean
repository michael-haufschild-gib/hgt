/-
# The parameter-space obstructed / viable sets — a formal home for the ∂𝒱 conjecture

Makes the objects of the critical-curve program formal sets in the `b`-plane:

* `Obstructed = {b | K_b meets the closed unit disk}` — proven CLOSED (projection of a closed
  joint set along the compact witness disk `D̄(0,1)`);
* `Viable = Obstructedᶜ` — open;
* `PatternRegion` — the preperiodic-entry region (subsuming the P1/P2/P3 patterns), proven `⊆
  Obstructed`;
* `ObstructedEqClosurePattern : Prop` — the standing conjecture `Obstructed = closure PatternRegion`
  as a NAMED proposition (a formal object for future work, not an axiom), a parameter-space
  disk-avoidance analog of the Mandelbrot set's boundary structure.

`frontier Obstructed` is the critical curve `ρ` as a formal set; the machine-checked slice
(`critical_curve_bracket`) and radial bracket (`lobe_radial_bracket`) are its first certified
points.
-/
import GaloisForLFunctions.U0.U0CurveSectors
import GaloisForLFunctions.U0.U0LobeInstances

open Complex Set Bottcher Metric Filter Topology

namespace U0ParameterSpace

/-- The iterate `(b,z) ↦ f_b^[n] z` is jointly continuous. -/
theorem continuous_iterate_pair (n : ℕ) :
    Continuous (fun p : ℂ × ℂ => (quadratic p.1)^[n] p.2) := by
  induction n with
  | zero => simpa using continuous_snd
  | succ n ih =>
    simp only [Function.iterate_succ_apply', quadratic_apply]
    exact (ih.pow 2).add continuous_fst

/-- **The obstructed set**: parameters whose filled Julia set meets the closed unit disk. -/
def Obstructed : Set ℂ := {b : ℂ | ∃ z : ℂ, ‖z‖ ≤ 1 ∧ z ∈ filledJulia b}

/-- **The viability set** `𝒱`: parameters whose filled Julia set avoids the closed unit disk. -/
def Viable : Set ℂ := Obstructedᶜ

theorem mem_viable_iff {b : ℂ} : b ∈ Viable ↔ ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b := by
  simp only [Viable, Obstructed, mem_compl_iff, mem_setOf_eq, not_exists, not_and]

/-- **`Obstructed` is closed.**  Sequential closedness: a limit of obstructed parameters keeps a
witness — the witnesses live in the compact disk `D̄(0,1)`, so a subsequence converges, and the
orbit-boundedness bound passes to the limit by joint continuity of the iterates. -/
theorem isClosed_obstructed : IsClosed Obstructed := by
  refine IsSeqClosed.isClosed ?_
  intro bs b hbs hb
  choose zs hzs using hbs
  -- witnesses zs n ∈ D̄(0,1) with zs n ∈ K_{bs n}
  have hzmem : ∀ n, zs n ∈ closedBall (0 : ℂ) 1 := fun n => by
    simpa [mem_closedBall, dist_zero_right] using (hzs n).1
  obtain ⟨z, hzball, φ, hφmono, hφlim⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq hzmem
  refine ⟨z, by simpa [mem_closedBall, dist_zero_right] using hzball, ?_⟩
  -- z ∈ K_b : ∀ n, ‖f_b^[n] z‖ ≤ max 2 ‖b‖
  rw [filledJulia_eq_iInter, mem_iInter]
  intro n
  simp only [mem_preimage, mem_closedBall, dist_zero_right]
  -- the subsequence of pairs (bs (φ i), zs (φ i)) → (b, z)
  have hbsub : Tendsto (fun i => bs (φ i)) atTop (nhds b) := hb.comp hφmono.tendsto_atTop
  have hpair : Tendsto (fun i => ((bs (φ i)), (zs (φ i)))) atTop (nhds (b, z)) :=
    hbsub.prodMk_nhds hφlim
  have hnorm : Tendsto (fun i => ‖(quadratic (bs (φ i)))^[n] (zs (φ i))‖) atTop
      (nhds ‖(quadratic b)^[n] z‖) :=
    (((continuous_iterate_pair n).tendsto (b, z)).comp hpair).norm
  have hbound : Tendsto (fun i => max 2 ‖bs (φ i)‖) atTop (nhds (max 2 ‖b‖)) :=
    tendsto_const_nhds.max hbsub.norm
  refine le_of_tendsto_of_tendsto' hnorm hbound (fun i => ?_)
  have hz := (hzs (φ i)).2
  rw [filledJulia_eq_iInter, mem_iInter] at hz
  have hmem := hz n
  simpa [mem_preimage, mem_closedBall, dist_zero_right] using hmem

/-- `Viable` is open. -/
theorem isOpen_viable : IsOpen Viable := isClosed_obstructed.isOpen_compl

/-- **The preperiodic pattern region.**  A parameter is in it when some point `y` preperiodic
under `f_b` has `‖y − b‖ ≤ 1` (`P1` = fixed point, `P2` = 2-cycle, `P3` = 3-cycle, and deeper). -/
def PatternRegion : Set ℂ :=
  {b : ℂ | ∃ (y : ℂ) (k n : ℕ), 1 ≤ n ∧
    (quadratic b)^[k + n] y = (quadratic b)^[k] y ∧ ‖y - b‖ ≤ 1}

/-- Every pattern parameter is obstructed. -/
theorem patternRegion_subset_obstructed : PatternRegion ⊆ Obstructed := by
  rintro b ⟨y, k, n, hn, hper, hcond⟩
  exact U0ObstructionPatterns.filledJulia_meets_unit_disk_preperiodic hn hper hcond

/-- The `s`-parameterized Cassini (P1) region is obstructed. -/
theorem cassini_subset_obstructed :
    {b : ℂ | ∃ s : ℂ, b = (1 - s ^ 2) / 4 ∧ ‖s - 3‖ * ‖s + 1‖ ≤ 4} ⊆ Obstructed := by
  rintro b ⟨s, rfl, hcond⟩
  exact U0CurveSectors.obstructed_of_s hcond

/-- **The standing conjecture, as a named proposition** (not an axiom, not a `sorry`): the
obstructed set is exactly the closure of the preperiodic pattern region — the parameter-space
disk-avoidance analog of the Mandelbrot set.  `patternRegion_subset_obstructed` +
`isClosed_obstructed` give `closure PatternRegion ⊆ Obstructed`; the reverse (density of pattern
parameters in `Obstructed`) is the open content. -/
def ObstructedEqClosurePattern : Prop := Obstructed = closure PatternRegion

/-- The easy half of the conjecture is a theorem: `closure PatternRegion ⊆ Obstructed`. -/
theorem closure_pattern_subset_obstructed : closure PatternRegion ⊆ Obstructed :=
  isClosed_obstructed.closure_subset_iff.mpr patternRegion_subset_obstructed

/-- The set of preperiodic points of `f_b`. -/
def Preperiodic (b : ℂ) : Set ℂ :=
  {p : ℂ | ∃ k n : ℕ, 1 ≤ n ∧ (quadratic b)^[k + n] p = (quadratic b)^[k] p}

/-- **Elementary reduction: a preperiodic point in the closed unit disk gives a pattern
parameter.**  If `p` is preperiodic with `‖p‖ ≤ 1`, then `y = f_b(p)` is preperiodic with
`‖y − b‖ = ‖p‖² ≤ 1`, so `b ∈ PatternRegion`. -/
theorem patternRegion_of_preperiodic_le_one {b p : ℂ} (hp : p ∈ Preperiodic b) (hnorm : ‖p‖ ≤ 1) :
    b ∈ PatternRegion := by
  obtain ⟨k, n, hn, hper⟩ := hp
  refine ⟨quadratic b p, k, n, hn, ?_, ?_⟩
  · have key : ∀ m : ℕ, (quadratic b)^[m] (quadratic b p) = (quadratic b)^[m + 1] p :=
      fun m => (Function.iterate_succ_apply (quadratic b) m p).symm
    have step : ∀ m : ℕ, quadratic b ((quadratic b)^[m] p) = (quadratic b)^[m + 1] p :=
      fun m => (Function.iterate_succ_apply' (quadratic b) m p).symm
    rw [key, key, ← step (k + n), ← step k, hper]
  · rw [quadratic_apply, add_sub_cancel_right, norm_pow]
    exact pow_le_one₀ (norm_nonneg p) hnorm

/-- **The reducible half of the conjecture (conditional on the classical density input).**  If the
preperiodic points of `f_b` are dense in `K_b` (classical — Fatou/Julia density of preperiodic
points, holds for the Cantor regime `b ∉ M`), then a parameter whose filled Julia set meets the
OPEN unit disk is a pattern parameter.  This banks the reduction and isolates the sole classical
input (`hdense`); the residual open core is the Fatou-interior-witness case not covered by density
in `J_b`. -/
theorem obstructed_open_sub_pattern_of_dense {b : ℂ}
    (hdense : filledJulia b ⊆ closure (Preperiodic b))
    (hb : ∃ z : ℂ, ‖z‖ < 1 ∧ z ∈ filledJulia b) :
    b ∈ PatternRegion := by
  obtain ⟨z, hz1, hzK⟩ := hb
  have hzcl : z ∈ closure (Preperiodic b) := hdense hzK
  obtain ⟨p, hp_pre, hp_close⟩ :=
    Metric.mem_closure_iff.mp hzcl (1 - ‖z‖) (by linarith)
  have hpnorm : ‖p‖ ≤ 1 := by
    have htri : ‖p‖ ≤ ‖z‖ + ‖p - z‖ := by
      calc ‖p‖ = ‖z + (p - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖p - z‖ := norm_add_le _ _
    rw [dist_eq_norm, norm_sub_rev] at hp_close
    linarith
  exact patternRegion_of_preperiodic_le_one hp_pre hpnorm

/-- A certified point of the obstructed set inside the window ring (the mid-angle 2-cycle). -/
theorem ringPoint_mem_obstructed : (⟨-33/25, 44/25⟩ : ℂ) ∈ Obstructed :=
  U0LobeInstances.lobe_obstructed_ring_127

/-- A preconnected set meeting both `t` and its complement meets `frontier t`. -/
theorem preconnected_inter_frontier {s t : Set ℂ} (hs : IsPreconnected s)
    (h1 : (s ∩ t).Nonempty) (h2 : (s ∩ tᶜ).Nonempty) : (s ∩ frontier t).Nonempty := by
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  have hVo : IsOpen (closure t)ᶜ := isClosed_closure.isOpen_compl
  have hsub : s ⊆ interior t ∪ (closure t)ᶜ := by
    intro x hx
    by_cases hcl : x ∈ closure t
    · left
      by_contra hxi
      have : x ∈ s ∩ frontier t := ⟨hx, hcl, hxi⟩
      rw [hcon] at this; exact this
    · right; exact hcl
  have hsu : (s ∩ interior t).Nonempty := by
    obtain ⟨p, hps, hpt⟩ := h1
    refine ⟨p, hps, ?_⟩
    by_contra hpi
    have : p ∈ s ∩ frontier t := ⟨hps, subset_closure hpt, hpi⟩
    rw [hcon] at this; exact this
  have hsv : (s ∩ (closure t)ᶜ).Nonempty := by
    obtain ⟨q, hqs, hqt⟩ := h2
    refine ⟨q, hqs, ?_⟩
    intro hqc
    have hqi : q ∉ interior t := fun hi => hqt (interior_subset hi)
    have : q ∈ s ∩ frontier t := ⟨hqs, hqc, hqi⟩
    rw [hcon] at this; exact this
  obtain ⟨w, _, hwu, hwv⟩ := hs (interior t) (closure t)ᶜ isOpen_interior hVo hsub hsu hsv
  exact hwv (subset_closure (interior_subset hwu))

/-- **A certified point of the critical curve `ρ = ∂Obstructed`.**  The radial bracket
(`lobe_radial_bracket`) pins a frontier point on the ray `arg b ≈ 126.9°` between the obstructed
`‖b‖ = 11/5` and the viable `‖b‖ = 22/5`: `ρ(126.9°) ∈ [11/5, 22/5]` — the first machine-checked
point of the parameter-space viability boundary as a formal set. -/
theorem exists_frontier_obstructed_on_ray :
    ∃ b : ℂ, b ∈ frontier Obstructed ∧
      b ∈ segment ℝ (⟨-33/25, 44/25⟩ : ℂ) (⟨-66/25, 88/25⟩ : ℂ) := by
  have hbo : (⟨-33/25, 44/25⟩ : ℂ) ∈ Obstructed := ringPoint_mem_obstructed
  have hbv : (⟨-66/25, 88/25⟩ : ℂ) ∈ Obstructedᶜ := by
    show (⟨-66/25, 88/25⟩ : ℂ) ∈ Viable
    rw [mem_viable_iff]
    refine U0CurveSectors.viable_of_gt_sharp ?_
    have hsq : ‖(⟨-66/25, 88/25⟩ : ℂ)‖ ^ 2 = 484 / 25 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; norm_num
    have hs2 : Real.sqrt 2 < 3 / 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    nlinarith [hsq, hs2, Real.sqrt_nonneg 2, norm_nonneg (⟨-66/25, 88/25⟩ : ℂ)]
  have hseg : IsPreconnected (segment ℝ (⟨-33/25, 44/25⟩ : ℂ) (⟨-66/25, 88/25⟩ : ℂ)) :=
    (convex_segment _ _).isPreconnected
  have h1 : (segment ℝ (⟨-33/25, 44/25⟩ : ℂ) (⟨-66/25, 88/25⟩ : ℂ) ∩ Obstructed).Nonempty :=
    ⟨_, left_mem_segment ℝ _ _, hbo⟩
  have h2 : (segment ℝ (⟨-33/25, 44/25⟩ : ℂ) (⟨-66/25, 88/25⟩ : ℂ) ∩ Obstructedᶜ).Nonempty :=
    ⟨_, right_mem_segment ℝ _ _, hbv⟩
  obtain ⟨b, hbseg, hbf⟩ := preconnected_inter_frontier hseg h1 h2
  exact ⟨b, hbf, hbseg⟩

/-- A certified point of the viable set (past the sharp threshold). -/
theorem sharpPoint_mem_viable : (⟨4, 0⟩ : ℂ) ∈ Viable := by
  rw [mem_viable_iff]
  refine U0CurveSectors.viable_of_gt_sharp ?_
  have hsq : ‖(⟨4, 0⟩ : ℂ)‖ ^ 2 = 16 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; norm_num
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  nlinarith [hsq, hs2, Real.sqrt_nonneg 2, norm_nonneg (⟨4, 0⟩ : ℂ)]

end U0ParameterSpace
