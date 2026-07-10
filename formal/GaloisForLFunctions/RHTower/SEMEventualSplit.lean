/-
# A fixed SEM annulus carries splits at every sufficiently large truncation

Uniform convergence is stronger than the existential domination theorem previously exposed by the
symmetrized Euler--Maclaurin API.  Once an isolating annulus is fixed, the target has a positive
boundary floor and the SEM error tends uniformly to zero.  Domination therefore holds for every
sufficiently large truncation, not merely for one selected member.

This module records that eventual form and performs the complete analytic split at each large
truncation on the same annulus.  It provides an honest discrete family on which a future `N -> 2N`
integral transition can be built; it does not assert any relation between that transition and the
algebraic `semHoleDefectZ` model.
-/
import GaloisForLFunctions.RHTower.FiniteMemberSteering

noncomputable section

namespace RHTower

open Complex Metric Filter

/-- Uniform decay toward a continuous nonvanishing target gives domination for every sufficiently
large member of the approximating family. -/
theorem eventually_domination_of_uniform_decay {K : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) {f : ℂ → ℂ} (hf : ContinuousOn f K)
    (hfne : ∀ z ∈ K, f z ≠ 0) {h : ℕ → ℂ → ℂ} {C σ : ℝ} (hσ : 0 < σ)
    (hbound : ∀ N : ℕ, 1 ≤ N → ∀ z ∈ K,
      ‖f z - h N z‖ ≤ C * (N : ℝ) ^ (-σ)) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ ∀ z ∈ K, ‖f z - h N z‖ < ‖h N z‖ := by
  obtain ⟨x, hxK, hmin⟩ := hK.exists_isMinOn hne hf.norm
  have hδ : 0 < ‖f x‖ := norm_pos_iff.mpr (hfne x hxK)
  have htend : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-σ)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hσ).comp
      tendsto_natCast_atTop_atTop).const_mul C
  have hhalf : 0 < ‖f x‖ / 2 := by positivity
  filter_upwards [htend.eventually (gt_mem_nhds hhalf), eventually_ge_atTop 1]
      with N hsmall hN
  refine ⟨hN, ?_⟩
  intro z hz
  have herr : ‖f z - h N z‖ ≤ C * (N : ℝ) ^ (-σ) := hbound N hN z hz
  have hfloor : ‖f x‖ ≤ ‖f z‖ := hmin hz
  have htri : ‖f z‖ ≤ ‖f z - h N z‖ + ‖h N z‖ := by
    calc
      ‖f z‖ = ‖f z - h N z + h N z‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

/-- Raw SEM domination holds eventually on any fixed isolating annulus. -/
theorem eventually_sem_domination_on_annulus {ρ : ℂ} {r₀ R : ℝ} (hr₀ : 0 < r₀)
    (hrR : r₀ < R)
    (hstrip : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ ∀ z ∈ closedBall ρ R \ ball ρ r₀,
      ‖2 * riemannZeta z - semCarrier N z‖ < ‖semCarrier N z‖ := by
  obtain ⟨C, σ, hσ, _hC, hbound⟩ := sem_uniform_decay_on_annulus hr₀ hrR hstrip
  have hKsub : closedBall ρ R \ ball ρ r₀ ⊆ closedBall ρ R := fun z hz => hz.1
  have hz1K : ∀ z ∈ closedBall ρ R \ ball ρ r₀, z ≠ 1 := by
    intro z hz h
    have hlt := (hstrip z (hKsub hz)).2
    rw [h] at hlt
    simp at hlt
  apply eventually_domination_of_uniform_decay
    ((isCompact_closedBall ρ R).diff isOpen_ball)
    (annulus_closed_nonempty hr₀.le hrR) (σ := σ) ?_ ?_ hσ hbound
  · intro z hz
    exact (continuousAt_const.mul
      (differentiableAt_riemannZeta (hz1K z hz)).continuousAt).continuousWithinAt
  · intro z hz
    have hzρ : z ≠ ρ := by
      intro h
      exact hz.2 (by rw [h]; exact mem_ball_self hr₀)
    have hζne : riemannZeta z ≠ 0 := by
      intro hζ0
      exact hiso z (hKsub hz) hzρ
        ((xi_eq_zero_iff (hstrip z (hKsub hz)).1 (hz1K z hz)).mpr hζ0)
    exact mul_ne_zero two_ne_zero hζne

/-- Completed SEM domination is exactly raw domination after cancelling the nonzero archimedean
factor on the open strip. -/
theorem completedSEM_domination_iff_raw {N : ℕ} {s : ℂ} (hσ : 0 < s.re) (h1 : s ≠ 1) :
    (‖xi s - completedSEM N s‖ < ‖completedSEM N s‖)
      ↔ (‖2 * riemannZeta s - semCarrier N s‖ < ‖semCarrier N s‖) := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hσ
  unfold completedSEM
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG]
  rw [show archFactor s * riemannZeta s - archFactor s * semCarrier N s / 2
      = (archFactor s / 2) * (2 * riemannZeta s)
        - (archFactor s / 2) * semCarrier N s from by ring]
  rw [show archFactor s * semCarrier N s / 2
      = (archFactor s / 2) * semCarrier N s from by ring]
  exact norm_mul_sub_lt_iff (div_ne_zero (archFactor_ne_zero h0 h1 hG) two_ne_zero)

/-- Completed SEM domination holds eventually on the two charts of any fixed isolating annulus. -/
theorem eventually_completedSEM_domination_on_annulus {ρ : ℂ} {r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hrR : r₀ < R)
    (hstrip : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧
      ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        ‖xi z - completedSEM N z‖ < ‖completedSEM N z‖ := by
  filter_upwards [eventually_sem_domination_on_annulus hr₀ hrR hstrip hiso]
      with N hN
  refine ⟨hN.1, ?_⟩
  intro z hz
  have hzK : z ∈ closedBall ρ R \ ball ρ r₀ := by
    rw [charts_union_eq_annulus ρ hr₀.le] at hz
    exact ⟨ball_subset_closedBall hz.1, fun hb => hz.2 (ball_subset_closedBall hb)⟩
  have hstripz := hstrip z hzK.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hstripz
    simp at hstripz
  exact (completedSEM_domination_iff_raw hstripz.1 hz1).mpr (hN.2 z hzK)

/-- **Eventual fixed-annulus SEM split supply.**  Around every strip point there is one isolating
annulus such that every sufficiently large symmetrized Euler--Maclaurin truncation dominates `xi`
and admits a complete split on that same annulus. -/
theorem semSplitData_eventually_exists (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ r₀ R : ℝ, 0 < r₀ ∧ r₀ < R ∧
      (∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0) ∧
      ∀ᶠ N : ℕ in atTop, ∃ (zs : List ℂ) (u : ℂ → ℂ),
        SEMSplitData ρ r₀ R N zs u := by
  obtain ⟨R₁, hR₁, hiso₁⟩ := xi_exists_isolating_radius ρ
  set R := min (R₁ / 2) (min (ρ.re / 2) ((1 - ρ.re) / 2)) with hRdef
  have hRpos : 0 < R := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hRR₁ : R < R₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRre : R ≤ ρ.re / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hRre1 : R ≤ (1 - ρ.re) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hstripcb : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre : |z.re - ρ.re| ≤ R := by
      have h := Complex.abs_re_le_norm (z - ρ)
      rw [Complex.sub_re] at h
      linarith
    rw [abs_le] at hre
    constructor
    · linarith [hre.1]
    · linarith [hre.2]
  have hisocb : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0 := by
    intro z hz
    apply hiso₁
    rw [mem_ball]
    rw [mem_closedBall] at hz
    linarith
  have hevent := eventually_completedSEM_domination_on_annulus
    (r₀ := R / 2) (by linarith) (by linarith) hstripcb hisocb
  refine ⟨R / 2, R, by linarith, by linarith, hstripcb, hisocb, ?_⟩
  filter_upwards [hevent] with N hN
  have hFan : AnalyticOnNhd ℂ (completedSEM N) (ball ρ R) := fun z hz =>
    completedSEM_analyticOnNhd_strip hN.1 z (hstripcb z (ball_subset_closedBall hz))
  obtain ⟨zs, u, hzs, huan, hune, hufact⟩ :=
    exists_split_of_domination (by linarith : (0 : ℝ) ≤ R / 2) (by linarith) hFan hN.2
  exact ⟨zs, u, by linarith, by linarith,
    fun z hz => hstripcb z (ball_subset_closedBall hz),
    fun z hz => hisocb z (ball_subset_closedBall hz), hzs, huan, hune, hufact, hN.2⟩

/-! ### Pairwise large-truncation transitions -/

/-- A uniformly convergent family is eventually pairwise relatively close on a compact set where
its target is nonvanishing.  The comparison is oriented: every large `M` lies inside the strict
Rouché ball centred at every large `N`. -/
theorem eventually_pairwise_relative_domination_of_uniform_decay
    {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    {f : ℂ → ℂ} (hf : ContinuousOn f K) (hfne : ∀ z ∈ K, f z ≠ 0)
    {h : ℕ → ℂ → ℂ} {C σ : ℝ} (hσ : 0 < σ)
    (hbound : ∀ N : ℕ, 1 ≤ N → ∀ z ∈ K,
      ‖f z - h N z‖ ≤ C * (N : ℝ) ^ (-σ)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N₀ ≤ M →
      1 ≤ N ∧ 1 ≤ M ∧ ∀ z ∈ K, ‖h M z - h N z‖ < ‖h N z‖ := by
  obtain ⟨x, hxK, hmin⟩ := hK.exists_isMinOn hne hf.norm
  have hδ : 0 < ‖f x‖ := norm_pos_iff.mpr (hfne x hxK)
  have htend : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-σ)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hσ).comp
      tendsto_natCast_atTop_atTop).const_mul C
  have hquarter : 0 < ‖f x‖ / 4 := by positivity
  have hevent : ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ (-σ) < ‖f x‖ / 4 ∧ 1 ≤ N :=
    (htend.eventually (gt_mem_nhds hquarter)).and (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨N₀, ?_⟩
  intro N hN M hM
  obtain ⟨hNsmall, hN1⟩ := hN₀ N hN
  obtain ⟨hMsmall, hM1⟩ := hN₀ M hM
  refine ⟨hN1, hM1, ?_⟩
  intro z hz
  have herrN : ‖f z - h N z‖ ≤ C * (N : ℝ) ^ (-σ) := hbound N hN1 z hz
  have herrM : ‖f z - h M z‖ ≤ C * (M : ℝ) ^ (-σ) := hbound M hM1 z hz
  have hdiff : ‖h M z - h N z‖ ≤ ‖f z - h M z‖ + ‖f z - h N z‖ := by
    calc
      ‖h M z - h N z‖ = ‖-(f z - h M z) + (f z - h N z)‖ := by
        congr 1
        ring
      _ ≤ _ := by simpa only [norm_neg] using
        norm_add_le (-(f z - h M z)) (f z - h N z)
  have hfloor : ‖f x‖ ≤ ‖f z‖ := hmin hz
  have htri : ‖f z‖ ≤ ‖f z - h N z‖ + ‖h N z‖ := by
    calc
      ‖f z‖ = ‖f z - h N z + h N z‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

/-- On a fixed isolating annulus, every two sufficiently large completed SEM members are relatively
close on both slit charts. -/
theorem eventually_pairwise_completedSEM_relative_domination_on_annulus
    {ρ : ℂ} {r₀ R : ℝ} (hr₀ : 0 < r₀) (hrR : r₀ < R)
    (hstrip : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N₀ ≤ M →
      1 ≤ N ∧ 1 ≤ M ∧ ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        ‖completedSEM M z - completedSEM N z‖ < ‖completedSEM N z‖ := by
  let K : Set ℂ := closedBall ρ R \ ball ρ r₀
  have hKcompact : IsCompact K := (isCompact_closedBall ρ R).diff isOpen_ball
  have hKne : K.Nonempty := annulus_closed_nonempty hr₀.le hrR
  have hKsub : K ⊆ closedBall ρ R := fun _ hz => hz.1
  have hxine : ∀ z ∈ K, xi z ≠ 0 := by
    intro z hz
    apply hiso z hz.1
    intro hzρ
    exact hz.2 (hzρ ▸ mem_ball_self hr₀)
  obtain ⟨C, σ, hσ, _hC, hbound⟩ := xi_sub_completedSEM_uniform_decay_on_compact
    hKcompact hKne (fun z hz => hstrip z (hKsub hz))
  obtain ⟨N₀, hN₀⟩ := eventually_pairwise_relative_domination_of_uniform_decay
    hKcompact hKne (f := xi) (h := completedSEM)
    (fun z _ => ((xi_analyticOnNhd Set.univ) z
      (Set.mem_univ z)).continuousAt.continuousWithinAt)
    hxine hσ hbound
  refine ⟨N₀, ?_⟩
  intro N hN M hM
  obtain ⟨hN1, hM1, hrel⟩ := hN₀ N hN M hM
  refine ⟨hN1, hM1, ?_⟩
  intro z hz
  apply hrel z
  rw [charts_union_eq_annulus ρ hr₀.le] at hz
  exact ⟨ball_subset_closedBall hz.1, fun hb => hz.2 (ball_subset_closedBall hb)⟩

/-- The straight-line transition between two completed SEM truncations. -/
def completedSEMLinearTransition (N M : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  completedSEM N z + (t : ℂ) * (completedSEM M z - completedSEM N z)

/-- Relative domination makes the entire straight-line transition nonvanishing at the boundary
point.  Thus every pair of sufficiently large truncations is joined by an actual zero-free
finite-to-finite annulus homotopy. -/
theorem completedSEMLinearTransition_ne_zero_of_relative_domination
    {N M : ℕ} {t : ℝ} {z : ℂ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hrel : ‖completedSEM M z - completedSEM N z‖ < ‖completedSEM N z‖) :
    completedSEMLinearTransition N M t z ≠ 0 := by
  apply left_ne_zero_of_norm_sub_lt (b := completedSEM N z)
  rw [completedSEMLinearTransition]
  have ht_norm : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  rw [show completedSEM N z + (t : ℂ) * (completedSEM M z - completedSEM N z) -
      completedSEM N z = (t : ℂ) * (completedSEM M z - completedSEM N z) by ring,
    norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht_norm) hrel

/-- **Fixed-annulus eventual family with zero-free finite transitions.**  At every strip point one
annulus simultaneously supports complete splits for all sufficiently large SEM truncations and a
zero-free straight-line boundary homotopy between every two sufficiently large members. -/
theorem semSplitData_eventually_exists_with_zeroFree_transitions
    (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ r₀ R : ℝ, 0 < r₀ ∧ r₀ < R ∧
      (∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0) ∧
      (∀ᶠ N : ℕ in atTop, ∃ (zs : List ℂ) (u : ℂ → ℂ),
        SEMSplitData ρ r₀ R N zs u) ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ, N₀ ≤ M →
        1 ≤ N ∧ 1 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
            completedSEMLinearTransition N M t z ≠ 0 := by
  obtain ⟨r₀, R, hr₀, hrR, hstrip, hiso, hsplits⟩ :=
    semSplitData_eventually_exists ρ h0 h1
  obtain ⟨N₀, hpair⟩ :=
    eventually_pairwise_completedSEM_relative_domination_on_annulus hr₀ hrR hstrip hiso
  refine ⟨r₀, R, hr₀, hrR, hstrip, hiso, hsplits, N₀, ?_⟩
  intro N hN M hM
  obtain ⟨hN1, hM1, hrel⟩ := hpair N hN M hM
  refine ⟨hN1, hM1, ?_⟩
  intro t ht z hz
  exact completedSEMLinearTransition_ne_zero_of_relative_domination ht (hrel z hz)

end RHTower
