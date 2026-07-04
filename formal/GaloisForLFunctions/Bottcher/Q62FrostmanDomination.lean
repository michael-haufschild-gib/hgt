/-
# q62 — GAP-A Half B (Frostman domination) on the Julia set, unconditional

Brick 1 of the Brolin-theorem formalization.  The truncated logarithmic potential of the
target-`a` Brolin measure is `≤ 0` at every Julia-frontier point, with no equilibrium/energy
theory and no Julia-nullity.  A frontier point `z` is a limit of basin points `u k`, where the
truncated kernel is dominated by the true kernel whose potential is `−G_c(u k) ≤ 0`; the
truncated integral is continuous along `u k → z`.  For disconnected `c` (`K_c = J_c`) this
discharges the `hnonpos` gate of `PotentialDominatedOnFilledJulia_of_truncatedLogKernel_inv_nat_nonpos`.
-/
import GaloisForLFunctions.Bottcher.Q62EquilibriumVanishing
import GaloisForLFunctions.Bottcher.CantorFilledJulia
open MeasureTheory Complex Filter Metric Set Topology
namespace Bottcher
noncomputable section

theorem truncatedLogKernel_symm (x w : ℂ) (d : ℝ) :
    truncatedLogKernel x d w = truncatedLogKernel w d x := by
  unfold truncatedLogKernel; rw [norm_sub_rev]

theorem integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_mem_frontier
    {c a z : ℂ} (hz : z ∈ frontier (filledJulia c)) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂(limitingBrolinMeasureAt c a) ≤ 0 := by
  set μ := limitingBrolinMeasureAt c a with hμdef
  haveI : IsProbabilityMeasure μ := instIsProbabilityMeasure_limitingBrolinMeasureAt c a
  set M : ℝ := max 2 ‖c‖ with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le two_pos (le_max_left _ _)
  have hzK : z ∈ filledJulia c := (isClosed_filledJulia c).frontier_subset hz
  have hKcarrier : ∀ᵐ w ∂μ, w ∈ filledJulia c := by
    rw [ae_iff]; simpa using (limitingBrolinMeasureAt_isProbOn_filledJulia c a).2
  have hwball : ∀ᵐ w ∂μ, ‖w‖ ≤ M := by
    filter_upwards [hKcarrier] with w hw
    have h := mem_closedBall.mp (filledJulia_subset_closedBall c hw)
    rwa [dist_zero_right] at h
  have hzcl : z ∈ closure (filledJulia c)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hz; exact hz.2
  obtain ⟨u, hucompl, hutend⟩ := mem_closure_iff_seq_limit.mp hzcl
  obtain ⟨Ru, hRu⟩ : ∃ Ru : ℝ, ∀ k, ‖u k‖ ≤ Ru := by
    obtain ⟨Ru, hRu⟩ := (hutend.norm).bddAbove_range
    exact ⟨Ru, fun k => hRu ⟨k, rfl⟩⟩
  set B : ℝ := |Real.log δ| + |Real.log (max δ (Ru + M))| with hBdef
  -- uniform a.e. bound on the truncated kernel for base points of norm ≤ Ru
  have hbnd : ∀ x : ℂ, ‖x‖ ≤ Ru → ∀ᵐ w ∂μ, ‖truncatedLogKernel x δ w‖ ≤ B := by
    intro x hx
    filter_upwards [hwball] with w hw
    have hle : ‖x - w‖ ≤ Ru + M := le_trans (norm_sub_le _ _) (add_le_add hx hw)
    have h1 : δ ≤ max δ ‖x - w‖ := le_max_left _ _
    have hmpos : 0 < max δ ‖x - w‖ := lt_of_lt_of_le hδ h1
    have h2 : max δ ‖x - w‖ ≤ max δ (Ru + M) := max_le_max le_rfl hle
    have hlogl : Real.log δ ≤ Real.log (max δ ‖x - w‖) := Real.log_le_log hδ h1
    have hlogu : Real.log (max δ ‖x - w‖) ≤ Real.log (max δ (Ru + M)) := Real.log_le_log hmpos h2
    unfold truncatedLogKernel
    rw [Real.norm_eq_abs, abs_neg]
    rw [abs_le]
    constructor
    · calc -B ≤ Real.log δ := by
              have : -|Real.log δ| ≤ Real.log δ := neg_abs_le _
              have hnn : 0 ≤ |Real.log (max δ (Ru + M))| := abs_nonneg _
              simp only [hBdef]; linarith
        _ ≤ _ := hlogl
    · calc Real.log (max δ ‖x - w‖) ≤ Real.log (max δ (Ru + M)) := hlogu
        _ ≤ |Real.log (max δ (Ru + M))| := le_abs_self _
        _ ≤ B := by simp only [hBdef]; linarith [abs_nonneg (Real.log δ)]
  have hintx : ∀ x : ℂ, ‖x‖ ≤ Ru → Integrable (fun w => truncatedLogKernel x δ w) μ :=
    fun x hx => Integrable.of_bound
      (continuous_truncatedLogKernel (z := x) hδ).aestronglyMeasurable B (hbnd x hx)
  -- value at each basin point u k is ≤ 0
  have hnonpos_seq : ∀ k, ∫ w, truncatedLogKernel (u k) δ w ∂μ ≤ 0 := by
    intro k
    have hukK : u k ∉ filledJulia c := hucompl k
    have hdpos : 0 < Metric.infDist (u k) (filledJulia c) :=
      ((isClosed_filledJulia c).notMem_iff_infDist_pos ⟨z, hzK⟩).mp hukK
    set d : ℝ := Metric.infDist (u k) (filledJulia c) with hddef
    have hne : ∀ᵐ w ∂μ, u k ≠ w := by
      filter_upwards [hKcarrier] with w hw h; exact hukK (h ▸ hw)
    have hlogInt : Integrable (fun w => logKernel (u k) w) μ := by
      have hmeas : AEStronglyMeasurable (fun w => logKernel (u k) w) μ :=
        (Real.measurable_log.comp ((continuous_const.sub continuous_id).norm.measurable)).neg.aestronglyMeasurable
      refine Integrable.of_bound hmeas (max |Real.log d| |Real.log (Ru + M)|) ?_
      filter_upwards [hKcarrier, hwball] with w hwK hwn
      have hdle : d ≤ ‖u k - w‖ := by
        simpa [Complex.dist_eq] using Metric.infDist_le_dist_of_mem hwK
      have hup : ‖u k - w‖ ≤ Ru + M := le_trans (norm_sub_le _ _) (add_le_add (hRu k) hwn)
      have hnpos : 0 < ‖u k - w‖ := lt_of_lt_of_le hdpos hdle
      unfold logKernel
      rw [Real.norm_eq_abs, abs_neg, abs_le]
      constructor
      · have : Real.log d ≤ Real.log ‖u k - w‖ := Real.log_le_log hdpos hdle
        calc -max |Real.log d| |Real.log (Ru + M)| ≤ -|Real.log d| :=
              neg_le_neg (le_max_left _ _)
          _ ≤ Real.log d := neg_abs_le _
          _ ≤ _ := this
      · have : Real.log ‖u k - w‖ ≤ Real.log (Ru + M) := Real.log_le_log hnpos hup
        calc Real.log ‖u k - w‖ ≤ Real.log (Ru + M) := this
          _ ≤ |Real.log (Ru + M)| := le_abs_self _
          _ ≤ _ := le_max_right _ _
    have hmono : (fun w => truncatedLogKernel (u k) δ w) ≤ᵐ[μ] (fun w => logKernel (u k) w) := by
      filter_upwards [hne] with w hw
      exact truncatedLogKernel_le_logKernel_of_ne hδ hw
    have hle_int : ∫ w, truncatedLogKernel (u k) δ w ∂μ ≤ ∫ w, logKernel (u k) w ∂μ :=
      integral_mono_ae (hintx (u k) (hRu k)) hlogInt hmono
    have hbasin : ∫ w, logKernel (u k) w ∂μ = - greenFunctionDyn c (u k) := by
      have := green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin (c := c) (a := a) hukK
      unfold logPotential at this
      linarith [this]
    rw [hbasin] at hle_int
    exact le_trans hle_int (by linarith [greenFunctionDyn_nonneg c (u k)])
  -- pass to the limit
  have hcont : Tendsto (fun k => ∫ w, truncatedLogKernel (u k) δ w ∂μ)
      atTop (𝓝 (∫ w, truncatedLogKernel z δ w ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B) ?_ (integrable_const B) ?_ ?_
    · exact fun k => (continuous_truncatedLogKernel (z := u k) hδ).aestronglyMeasurable
    · exact fun k => hbnd (u k) (hRu k)
    · filter_upwards with w
      have hsymm : ∀ x : ℂ, truncatedLogKernel x δ w = truncatedLogKernel w δ x :=
        fun x => truncatedLogKernel_symm x w δ
      simp only [hsymm]
      exact ((continuous_truncatedLogKernel (z := w) hδ).continuousAt).tendsto.comp hutend
  exact le_of_tendsto hcont (Filter.Eventually.of_forall hnonpos_seq)

/-- **Half B (Frostman domination) for empty-interior `K_c`, from brick 1.**  When the filled
Julia set has empty interior (`filledJulia c ⊆ frontier`, e.g. every disconnected `c` and every
dendrite such as `c = −2`), every `K_c` point is a frontier point, so brick 1 discharges the
truncated-nonpositivity gate on all of `K_c`; with atom-freeness this gives the full
`PotentialDominatedOnFilledJulia` — Half B unconditional on this locus, no equilibrium theory. -/
theorem potentialDominatedOnFilledJulia_of_subset_frontier_of_atomless {c a : ℂ}
    (hsub : filledJulia c ⊆ frontier (filledJulia c))
    (hatom : ∀ z : ℂ, z ∈ filledJulia c → limitingBrolinMeasureAt c a {z} = 0) :
    PotentialDominatedOnFilledJulia c a :=
  PotentialDominatedOnFilledJulia_of_truncatedLogKernel_inv_nat_nonpos hatom
    (fun z hz _n =>
      integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_mem_frontier
        (hsub hz) (by positivity))

/-- **Brick 2: pointwise Frostman domination `Uᵘ ≤ 0` at any Julia-frontier point** (all `c`,
both-connected included), given the measure has no atom there.  Upgrades the truncated brick 1 to
the full logarithmic potential via dominated convergence of the `1/(n+1)` truncations.  This is the
boundary half of Half B for the consumer-relevant regime. -/
theorem logPotential_limitingBrolinMeasureAt_nonpos_of_mem_frontier_of_atom
    {c a z : ℂ} (hz : z ∈ frontier (filledJulia c))
    (hatom : limitingBrolinMeasureAt c a {z} = 0) :
    logPotential (limitingBrolinMeasureAt c a) z ≤ 0 := by
  by_cases hint : Integrable (fun w => logKernel z w) (limitingBrolinMeasureAt c a)
  · have hne_ae : ∀ᵐ w ∂(limitingBrolinMeasureAt c a), w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 (by simpa using hatom)
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂limitingBrolinMeasureAt c a)
          atTop (𝓝 (logPotential (limitingBrolinMeasureAt c a) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · exact fun n => (continuous_truncatedLogKernel (z := z) (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 :=
          inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne (fun hzw => hw hzw.symm)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall
      (fun n => integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_mem_frontier
        hz (by positivity)))
  · have : logPotential (limitingBrolinMeasureAt c a) z = 0 := by
      unfold logPotential; exact integral_undef hint
    rw [this]

/-- **Atomlessness on the Julia set, unconditional.**  Brick 1 (truncated domination) is exactly
the hypothesis of Codex's atom-pressure lemma, so the Brolin measure has no atom at any
Julia-frontier point — no `CriticalOrbitAvoidingTarget`, no equidistribution. -/
theorem limitingBrolinMeasureAt_singleton_eq_zero_of_mem_frontier
    {c a z : ℂ} (hz : z ∈ frontier (filledJulia c)) :
    limitingBrolinMeasureAt c a {z} = 0 :=
  limitingBrolinMeasureAt_singleton_eq_zero_of_truncatedLogKernel_nonpos
    ((isClosed_filledJulia c).frontier_subset hz)
    (fun {_δ} hδ _ => integral_truncatedLogKernel_limitingBrolinMeasureAt_nonpos_of_mem_frontier hz hδ)

/-- **Pointwise Frostman domination on `J_c`, fully unconditional** (all `c`).  Brick 2 with the
atom hypothesis now discharged internally. -/
theorem logPotential_limitingBrolinMeasureAt_nonpos_of_mem_frontier
    {c a z : ℂ} (hz : z ∈ frontier (filledJulia c)) :
    logPotential (limitingBrolinMeasureAt c a) z ≤ 0 :=
  logPotential_limitingBrolinMeasureAt_nonpos_of_mem_frontier_of_atom hz
    (limitingBrolinMeasureAt_singleton_eq_zero_of_mem_frontier hz)

/-- **Half B unconditional for empty-interior `K_c`.**  Only the empty-interior hypothesis remains;
atom-freeness is now automatic.  Covers every disconnected `c` and every dendrite (e.g. `c = −2`). -/
theorem potentialDominatedOnFilledJulia_of_subset_frontier {c a : ℂ}
    (hsub : filledJulia c ⊆ frontier (filledJulia c)) :
    PotentialDominatedOnFilledJulia c a :=
  potentialDominatedOnFilledJulia_of_subset_frontier_of_atomless hsub
    (fun _ hz => limitingBrolinMeasureAt_singleton_eq_zero_of_mem_frontier (hsub hz))

/-! ### Concrete unconditional Half B for `‖c‖ ≥ 4` (large disconnected parameters) -/

/-- A totally-disconnected subset of `ℂ` has empty interior: a ball of positive radius is
preconnected with more than one point, contradicting total disconnectedness. -/
theorem interior_eq_empty_of_isTotallyDisconnected_complex {E : Set ℂ}
    (hE : IsTotallyDisconnected E) : interior E = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
  have hballE : Metric.ball z r ⊆ E := hball.trans interior_subset
  have hss : (Metric.ball z r).Subsingleton := hE _ hballE (convex_ball z r).isPreconnected
  have h1 : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have h2 : z + ((r / 2 : ℝ) : ℂ) ∈ Metric.ball z r := by
    have hd : dist (z + ((r / 2 : ℝ) : ℂ)) z = r / 2 := by
      rw [Complex.dist_eq]
      have he : (z + ((r / 2 : ℝ) : ℂ)) - z = ((r / 2 : ℝ) : ℂ) := by ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < r/2 by positivity)]
    rw [Metric.mem_ball, hd]; linarith
  have heq : z = z + ((r / 2 : ℝ) : ℂ) := hss h1 h2
  have h0 : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -heq
  have : (r / 2 : ℝ) = 0 := by exact_mod_cast h0
  linarith

/-- A closed set with empty interior is contained in its frontier (indeed equals it). -/
theorem filledJulia_subset_frontier_of_interior_empty {c : ℂ}
    (h : interior (filledJulia c) = ∅) :
    filledJulia c ⊆ frontier (filledJulia c) := by
  have hf : frontier (filledJulia c) = filledJulia c := by
    rw [frontier, (isClosed_filledJulia c).closure_eq, h, Set.diff_empty]
  rw [hf]

/-- `K_c` has empty interior for `‖c‖ ≥ 4` (Cantor regime). -/
theorem interior_filledJulia_eq_empty_of_four_le {c : ℂ} (hc : 4 ≤ ‖c‖) :
    interior (filledJulia c) = ∅ :=
  interior_eq_empty_of_isTotallyDisconnected_complex (isTotallyDisconnected_filledJulia_of_four_le hc)

/-- **Half B (Frostman domination) fully unconditional for `‖c‖ ≥ 4`.**  Large disconnected
parameters have Cantor (empty-interior) filled Julia sets, so brick 1's frontier domination
covers all of `K_c`. -/
theorem potentialDominatedOnFilledJulia_of_four_le {c a : ℂ} (hc : 4 ≤ ‖c‖) :
    PotentialDominatedOnFilledJulia c a :=
  potentialDominatedOnFilledJulia_of_subset_frontier
    (filledJulia_subset_frontier_of_interior_empty (interior_filledJulia_eq_empty_of_four_le hc))

end
end Bottcher