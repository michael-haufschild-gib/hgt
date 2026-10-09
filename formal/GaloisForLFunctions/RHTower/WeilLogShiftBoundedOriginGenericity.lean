import GaloisForLFunctions.RHTower.WeilLogShiftOriginDiagonalDivergence
import GaloisForLFunctions.RHTower.WeilLogShiftKernelTailOrder

/-!
# Generic nowhere bounded moments in the unit recovery cube

The origin inverse diagonal tends to infinity. Prefix-preserving antipodal
extensions therefore make every strict absolute origin tail excursion open
and dense. Countable intersection gives unbounded origin terms generically;
outward kernel domination transfers this to every real shift on the same set.
Even eventual boundedness at one history-dependent shift is a meagre exception.
No one-sided origin conclusion is asserted.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- Smooth cutoff suppression forces the origin inverse diagonal to infinity. -/
theorem tendsto_weilLogShiftRecoveryDiagonal_origin_atTop :
    Tendsto (fun k => weilLogShiftRecoveryMomentResponse 0 (k + 2) k) atTop atTop := by
  obtain ⟨c, γ, hc, hγ, hlower⟩ := exists_weilLogShiftOriginDiagonal_exponential_lower
  have harg : Tendsto (fun k : ℕ => γ * (k + 2 : ℕ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    have hscaled := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hγ
    filter_upwards [hscaled.eventually_ge_atTop B] with k hk
    have hk2 : (k : ℝ) ≤ (k + 2 : ℕ) := by
      exact_mod_cast (show k ≤ k + 2 by omega)
    exact hk.trans (mul_le_mul_of_nonneg_left hk2 hγ.le)
  exact tendsto_atTop_mono' atTop hlower
    ((tendsto_exp_atTop.comp harg).const_mul_atTop hc)

/-- Any finite bounded prefix admits a bounded extension whose absolute origin
terms tend to infinity, with the harmless first two indices omitted. -/
theorem exists_weilLogShiftBoundedHistory_prefix_origin_norm_atTop
    (height : WeilLogShiftBoundedHistory) (M : ℕ) :
    ∃ extended : WeilLogShiftBoundedHistory,
      (∀ k : ℕ, k < M → extended k = height k) ∧
      Tendsto (fun k => ‖weilLogShiftRecoveryMoment 0
        (weilLogShiftBoundedHistoryValues extended) (k + 2)‖) atTop atTop := by
  obtain ⟨extended, hprefix, _, hminor⟩ :=
    exists_weilLogShiftBoundedHistory_prefix_diagonal_minorant height M
  refine ⟨extended, hprefix, tendsto_atTop_mono' atTop ?_
    tendsto_weilLogShiftRecoveryDiagonal_origin_atTop⟩
  filter_upwards [eventually_ge_atTop M] with k hk
  exact hminor k hk 0

/-- Some absolute origin term beyond the chosen cutoff exceeds the threshold. -/
def weilLogShiftBoundedOriginTailExcursion (K N : ℕ) : Set WeilLogShiftBoundedHistory :=
  {height | ∃ n : ℕ, N + 2 ≤ n ∧ (K : ℝ) <
    ‖weilLogShiftRecoveryMoment 0 (weilLogShiftBoundedHistoryValues height) n‖}

theorem isOpen_weilLogShiftBoundedOriginTailExcursion (K N : ℕ) :
    IsOpen (weilLogShiftBoundedOriginTailExcursion K N) := by
  have hset : weilLogShiftBoundedOriginTailExcursion K N =
      ⋃ n : ℕ, ⋃ (_ : N + 2 ≤ n),
        {height : WeilLogShiftBoundedHistory | (K : ℝ) <
          ‖weilLogShiftRecoveryMoment 0 (weilLogShiftBoundedHistoryValues height) n‖} := by
    ext height
    simp only [weilLogShiftBoundedOriginTailExcursion, Set.mem_setOf_eq, Set.mem_iUnion,
      exists_prop]
  rw [hset]
  refine isOpen_iUnion fun n => isOpen_iUnion fun _ => isOpen_lt continuous_const ?_
  exact ((continuous_weilLogShiftRecoveryOriginTerm n).comp
    continuous_weilLogShiftBoundedHistoryValues).norm

theorem dense_weilLogShiftBoundedOriginTailExcursion (K N : ℕ) :
    Dense (weilLogShiftBoundedOriginTailExcursion K N) := by
  intro height
  choose extended hprefix hgrowth using
    (fun M : ℕ => exists_weilLogShiftBoundedHistory_prefix_origin_norm_atTop height M)
  have hlim : Tendsto extended atTop (𝓝 height) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => height k) atTop (𝓝 (height k))).congr'
    apply eventually_atTop.mpr
    exact ⟨k + 1, fun M hM => (hprefix M k (by omega)).symm⟩
  apply mem_closure_of_tendsto hlim
  filter_upwards with M
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hgrowth M).eventually_gt_atTop (K : ℝ))
  exact ⟨N + T + 2, by omega, hT (N + T) (by omega)⟩

/-- Absolute origin terms exceed every real threshold in every tail. -/
def WeilLogShiftBoundedOriginUnbounded (height : WeilLogShiftBoundedHistory) : Prop :=
  ∀ (B : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ B <
    ‖weilLogShiftRecoveryMoment 0 (weilLogShiftBoundedHistoryValues height) n‖

/-- Arbitrarily large absolute origin excursions are generic inside the fixed
unit cube, despite all recovery probes being bounded by one. -/
theorem dense_and_residual_weilLogShiftBoundedOriginUnbounded :
    Dense {height : WeilLogShiftBoundedHistory | WeilLogShiftBoundedOriginUnbounded height} ∧
      {height : WeilLogShiftBoundedHistory | WeilLogShiftBoundedOriginUnbounded height} ∈
        residual WeilLogShiftBoundedHistory := by
  have h := GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall
    (fun q : ℕ × ℕ => weilLogShiftBoundedOriginTailExcursion q.1 q.2)
    (fun q => isOpen_weilLogShiftBoundedOriginTailExcursion q.1 q.2)
    (fun q => dense_weilLogShiftBoundedOriginTailExcursion q.1 q.2)
  have hsub : {height : WeilLogShiftBoundedHistory | ∀ q : ℕ × ℕ,
      height ∈ weilLogShiftBoundedOriginTailExcursion q.1 q.2} ⊆
      {height | WeilLogShiftBoundedOriginUnbounded height} := by
    intro height hh B N
    obtain ⟨K, hK⟩ := exists_nat_gt B
    obtain ⟨n, hn, hlarge⟩ := hh (K, N)
    exact ⟨n, by omega, hK.trans hlarge⟩
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Absolute moments are unbounded in every tail at every real shift. -/
def WeilLogShiftBoundedNowhereBounded (height : WeilLogShiftBoundedHistory) : Prop :=
  ∀ (y B : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ B <
    ‖weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height) n‖

/-- Outward kernel comparison transfers origin excursions to all shifts
simultaneously, without a countable restriction on the shift parameter. -/
theorem weilLogShiftBoundedNowhereBounded_of_origin
    {height : WeilLogShiftBoundedHistory} (hh : WeilLogShiftBoundedOriginUnbounded height) :
    WeilLogShiftBoundedNowhereBounded height := by
  intro y B N
  by_cases hy : y = 0
  · simpa only [hy] using hh B N
  have h0y : |(0 : ℝ)| < |y| := by simpa only [abs_zero] using abs_pos.mpr hy
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_mul_pairedLogKernel_le_of_abs_lt h0y 1)
  obtain ⟨n, hn, hlarge⟩ := hh B (max N T)
  refine ⟨n, (le_max_left _ _).trans hn, hlarge.trans_le ?_⟩
  have hkernel : pairedLogKernel 0 n ≤ pairedLogKernel y n := by
    simpa only [one_mul] using hT n ((le_max_right _ _).trans hn)
  simp only [weilLogShiftRecoveryMoment, Real.norm_eq_abs, abs_mul,
    abs_of_pos (pairedLogKernel_pos 0 n), abs_of_pos (pairedLogKernel_pos y n)]
  exact mul_le_mul_of_nonneg_left hkernel (abs_nonneg _)

/-- Generic bounded histories have unbounded absolute weighted terms at every
real shift, a stronger conclusion than failure of moment summability. -/
theorem dense_and_residual_weilLogShiftBoundedNowhereBounded :
    Dense {height : WeilLogShiftBoundedHistory | WeilLogShiftBoundedNowhereBounded height} ∧
      {height : WeilLogShiftBoundedHistory | WeilLogShiftBoundedNowhereBounded height} ∈
        residual WeilLogShiftBoundedHistory := by
  have hsub : {height : WeilLogShiftBoundedHistory | WeilLogShiftBoundedOriginUnbounded height} ⊆
      {height | WeilLogShiftBoundedNowhereBounded height} :=
    fun _ hh => weilLogShiftBoundedNowhereBounded_of_origin hh
  have h := dense_and_residual_weilLogShiftBoundedOriginUnbounded
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

theorem weilLogShiftBounded_nowhere_summable_of_nowhere_bounded
    {height : WeilLogShiftBoundedHistory} (hh : WeilLogShiftBoundedNowhereBounded height) :
    ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height)) := by
  intro y hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hs.norm.tendsto_atTop_zero).2 1 (by norm_num))
  obtain ⟨n, hn, hlarge⟩ := hh y 1 N
  exact (not_lt_of_ge hlarge.le) (hN n hn)

/-- Nowhere signed summability is dense and residual even in the unit cube. -/
theorem dense_and_residual_weilLogShiftBounded_nowhere_summable :
    Dense {height : WeilLogShiftBoundedHistory | ∀ y : ℝ,
      ¬ Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height))} ∧
      {height : WeilLogShiftBoundedHistory | ∀ y : ℝ,
        ¬ Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height))} ∈
          residual WeilLogShiftBoundedHistory := by
  have hsub : {height : WeilLogShiftBoundedHistory | WeilLogShiftBoundedNowhereBounded height} ⊆
      {height | ∀ y : ℝ, ¬ Summable
        (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height))} :=
    fun _ hh => weilLogShiftBounded_nowhere_summable_of_nowhere_bounded hh
  have h := dense_and_residual_weilLogShiftBoundedNowhereBounded
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Even eventual boundedness at one history-dependent real shift is meagre. -/
theorem isMeagre_weilLogShiftBounded_some_eventually_bounded_moment :
    IsMeagre {height : WeilLogShiftBoundedHistory | ∃ y B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ‖weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height) n‖ ≤ B} := by
  change _ᶜ ∈ residual WeilLogShiftBoundedHistory
  apply mem_of_superset dense_and_residual_weilLogShiftBoundedNowhereBounded.2
  rintro height hh ⟨y, B, N, hbound⟩
  obtain ⟨n, hn, hlarge⟩ := hh y B N
  exact (not_lt_of_ge (hbound n hn)) hlarge

/-- Having any summable signed moment, at any real shift, is a meagre condition
on the unit cube. The shift may depend on the history. -/
theorem isMeagre_weilLogShiftBounded_some_summable_moment :
    IsMeagre {height : WeilLogShiftBoundedHistory | ∃ y : ℝ,
      Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height))} := by
  change _ᶜ ∈ residual WeilLogShiftBoundedHistory
  apply mem_of_superset dense_and_residual_weilLogShiftBounded_nowhere_summable.2
  rintro height hh ⟨y, hs⟩
  exact hh y hs

end RHTower
