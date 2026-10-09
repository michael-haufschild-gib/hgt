import GaloisForLFunctions.RHTower.WeilLogShiftUniformBallPerturbation

/-!
# Generic divergence under uniformly small observation errors

In every positive-radius closed supremum ball of bounded recovery histories,
absolute moment terms are generically unbounded in every tail at every real
shift. Eventual boundedness or signed summability at even one shift is meagre.
Thus arbitrary bounded observations admit uniformly arbitrarily small errors
with nowhere bounded reconstructed moments.
-/

open Filter Topology Zeta23 Real
open scoped BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- A strict absolute origin excursion in a closed supremum ball. -/
def weilLogShiftUniformBallTailExcursion (center : ℕ →ᵇ ℝ) (r : ℝ) (K N : ℕ) :
    Set (WeilLogShiftUniformHistoryBall center r) :=
  {h | ∃ n : ℕ, N + 2 ≤ n ∧ (K : ℝ) <
    ‖weilLogShiftRecoveryMoment 0 (h : ℕ →ᵇ ℝ) n‖}

theorem isOpen_weilLogShiftUniformBallTailExcursion (center : ℕ →ᵇ ℝ) (r : ℝ) (K N : ℕ) :
    IsOpen (weilLogShiftUniformBallTailExcursion center r K N) := by
  have hset : weilLogShiftUniformBallTailExcursion center r K N =
      ⋃ n : ℕ, ⋃ (_ : N + 2 ≤ n),
        {h : WeilLogShiftUniformHistoryBall center r | (K : ℝ) <
          ‖weilLogShiftRecoveryMoment 0 (h : ℕ →ᵇ ℝ) n‖} := by
    ext h
    simp only [weilLogShiftUniformBallTailExcursion, Set.mem_setOf_eq, Set.mem_iUnion,
      exists_prop]
  rw [hset]
  exact isOpen_iUnion fun n => isOpen_iUnion fun _ => isOpen_lt continuous_const
    (((continuous_weilLogShiftRecoveryMomentBCF 0 n).comp continuous_subtype_val).norm)

theorem dense_weilLogShiftUniformBallTailExcursion
    (center : ℕ →ᵇ ℝ) (r : ℝ) (hr : 0 < r) (K N : ℕ) :
    Dense (weilLogShiftUniformBallTailExcursion center r K N) := by
  apply Metric.dense_iff.mpr
  intro h ε hε
  obtain ⟨g, hnear, hlarge⟩ :=
    exists_weilLogShiftUniformBall_near_large_origin center r hr h K N ε hε
  exact ⟨g, hnear, hlarge⟩

/-- Every real-shift moment has arbitrarily large absolute terms in every tail. -/
def WeilLogShiftUniformNowhereBounded (h : ℕ →ᵇ ℝ) : Prop :=
  ∀ (y B : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ B < ‖weilLogShiftRecoveryMoment y h n‖

/-- Origin tail unboundedness transfers to every real shift for any bounded history. -/
theorem weilLogShiftUniformNowhereBounded_of_origin (h : ℕ →ᵇ ℝ)
    (hh : ∀ (B : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ B < ‖weilLogShiftRecoveryMoment 0 h n‖) :
    WeilLogShiftUniformNowhereBounded h := by
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

/-- Generic divergence persists in every positive-radius closed supremum ball,
including balls around arbitrary bounded histories and their boundary points. -/
theorem dense_and_residual_weilLogShiftUniformBall_nowhere_bounded
    (center : ℕ →ᵇ ℝ) (r : ℝ) (hr : 0 < r) :
    Dense {h : WeilLogShiftUniformHistoryBall center r |
      WeilLogShiftUniformNowhereBounded (h : ℕ →ᵇ ℝ)} ∧
      {h : WeilLogShiftUniformHistoryBall center r |
        WeilLogShiftUniformNowhereBounded (h : ℕ →ᵇ ℝ)} ∈
          residual (WeilLogShiftUniformHistoryBall center r) := by
  letI : CompleteSpace (WeilLogShiftUniformHistoryBall center r) :=
    Metric.isClosed_closedBall.completeSpace_coe
  have h := GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall
    (fun q : ℕ × ℕ => weilLogShiftUniformBallTailExcursion center r q.1 q.2)
    (fun q => isOpen_weilLogShiftUniformBallTailExcursion center r q.1 q.2)
    (fun q => dense_weilLogShiftUniformBallTailExcursion center r hr q.1 q.2)
  have hsub : {h : WeilLogShiftUniformHistoryBall center r | ∀ q : ℕ × ℕ,
      h ∈ weilLogShiftUniformBallTailExcursion center r q.1 q.2} ⊆
      {h | WeilLogShiftUniformNowhereBounded (h : ℕ →ᵇ ℝ)} := by
    intro height hh
    apply weilLogShiftUniformNowhereBounded_of_origin
    intro B N
    obtain ⟨K, hK⟩ := exists_nat_gt B
    obtain ⟨n, hn, hlarge⟩ := hh (K, N)
    exact ⟨n, by omega, hK.trans hlarge⟩
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

theorem weilLogShiftUniform_nowhere_summable_of_nowhere_bounded
    {h : ℕ →ᵇ ℝ} (hh : WeilLogShiftUniformNowhereBounded h) :
    ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y h) := by
  intro y hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hs.norm.tendsto_atTop_zero).2 1 (by norm_num))
  obtain ⟨n, hn, hlarge⟩ := hh y 1 N
  exact (not_lt_of_ge hlarge.le) (hN n hn)

/-- Nowhere signed summability is generic in every positive-radius uniform ball. -/
theorem dense_and_residual_weilLogShiftUniformBall_nowhere_summable
    (center : ℕ →ᵇ ℝ) (r : ℝ) (hr : 0 < r) :
    Dense {h : WeilLogShiftUniformHistoryBall center r | ∀ y : ℝ,
      ¬ Summable (weilLogShiftRecoveryMoment y (h : ℕ →ᵇ ℝ))} ∧
      {h : WeilLogShiftUniformHistoryBall center r | ∀ y : ℝ,
        ¬ Summable (weilLogShiftRecoveryMoment y (h : ℕ →ᵇ ℝ))} ∈
          residual (WeilLogShiftUniformHistoryBall center r) := by
  have hsub : {h : WeilLogShiftUniformHistoryBall center r |
      WeilLogShiftUniformNowhereBounded (h : ℕ →ᵇ ℝ)} ⊆
      {h | ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y (h : ℕ →ᵇ ℝ))} :=
    fun _ hh => weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hh
  have h := dense_and_residual_weilLogShiftUniformBall_nowhere_bounded center r hr
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Eventual boundedness at any history-dependent shift is meagre in every
positive-radius closed uniform ball. -/
theorem isMeagre_weilLogShiftUniformBall_some_eventually_bounded_moment
    (center : ℕ →ᵇ ℝ) (r : ℝ) (hr : 0 < r) :
    IsMeagre {h : WeilLogShiftUniformHistoryBall center r |
      ∃ y B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ‖weilLogShiftRecoveryMoment y (h : ℕ →ᵇ ℝ) n‖ ≤ B} := by
  change _ᶜ ∈ residual (WeilLogShiftUniformHistoryBall center r)
  apply mem_of_superset (dense_and_residual_weilLogShiftUniformBall_nowhere_bounded center r hr).2
  rintro h hh ⟨y, B, N, hbound⟩
  obtain ⟨n, hn, hlarge⟩ := hh y B N
  exact (not_lt_of_ge (hbound n hn)) hlarge

/-- Any finite signed moment is a meagre exception inside every uniform ball. -/
theorem isMeagre_weilLogShiftUniformBall_some_summable_moment
    (center : ℕ →ᵇ ℝ) (r : ℝ) (hr : 0 < r) :
    IsMeagre {h : WeilLogShiftUniformHistoryBall center r | ∃ y : ℝ,
      Summable (weilLogShiftRecoveryMoment y (h : ℕ →ᵇ ℝ))} := by
  change _ᶜ ∈ residual (WeilLogShiftUniformHistoryBall center r)
  apply mem_of_superset (dense_and_residual_weilLogShiftUniformBall_nowhere_summable center r hr).2
  rintro h hh ⟨y, hs⟩
  exact hh y hs

/-- Every bounded observation history admits arbitrarily small uniform errors
whose reconstructed moment terms are unbounded at every real shift. -/
theorem exists_weilLogShiftUniform_near_nowhere_bounded
    (center : ℕ →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℕ →ᵇ ℝ, ‖h - center‖ < ε ∧ WeilLogShiftUniformNowhereBounded h := by
  have hr : 0 < ε / 2 := by positivity
  let c : WeilLogShiftUniformHistoryBall center (ε / 2) :=
    ⟨center, by simpa only [Metric.mem_closedBall, dist_self] using hr.le⟩
  obtain ⟨h, _, hbad⟩ := Metric.dense_iff.mp
    (dense_and_residual_weilLogShiftUniformBall_nowhere_bounded center (ε / 2) hr).1
      c 1 zero_lt_one
  refine ⟨h, ?_, hbad⟩
  have hbound : ‖(h : ℕ →ᵇ ℝ) - center‖ ≤ ε / 2 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using h.property
  exact hbound.trans_lt (by linarith only [hε])

end RHTower
