import GaloisForLFunctions.RHTower.WeilLogShiftGenericMomentDivergence
import GaloisForLFunctions.RHTower.WeilLogShiftBoundedRecoveryNoGo

/-!
# Generic divergence inside the bounded recovery cube

Finite bounded prefixes admit bounded antipodal extensions with persistent
log-2-weighted terms. Their strict tail events are open and dense in the compact
product cube. Signed, excess, and deficit summability at log 2 are equivalent
throughout this cube, and fail generically. Inward transfer excludes every outer
shift |y| >= log 2 on the same dense residual set. Interior shifts are not settled.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- Recovery histories with every coordinate in the fixed closed unit interval. -/
abbrev WeilLogShiftBoundedHistory := ℕ → Set.Icc (-1 : ℝ) 1

def weilLogShiftBoundedHistoryValues (height : WeilLogShiftBoundedHistory) : ℕ → ℝ :=
  fun k => (height k : ℝ)

theorem continuous_weilLogShiftBoundedHistoryValues :
    Continuous weilLogShiftBoundedHistoryValues :=
  continuous_pi fun k => continuous_subtype_val.comp (continuous_apply k)

/-- The absolute weighted term at the first nontrivial integer-log shift. -/
def weilLogShiftBoundedHistoryTerm (height : WeilLogShiftBoundedHistory) (n : ℕ) : ℝ :=
  |weilDeviation (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n| *
    pairedLogKernel (log 2) n

theorem continuous_weilLogShiftBoundedHistoryTerm (n : ℕ) :
    Continuous (fun height : WeilLogShiftBoundedHistory =>
      weilLogShiftBoundedHistoryTerm height n) :=
  ((continuous_weilDeviation_recoveryInverse n).comp
    continuous_weilLogShiftBoundedHistoryValues).abs.mul_const _

theorem weilLogShiftBoundedHistory_probe_bound (height : WeilLogShiftBoundedHistory)
    (n : ℕ) (hn : 2 ≤ n) :
    |weilLogShiftRecoveryProbe
      (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n| ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  change |weilLogShiftRecoveryHistory
    (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) k| ≤ 1
  rw [weilLogShiftRecoveryHistory_inverse]
  exact abs_le.mpr (height k).property

/-- Every finite bounded prefix has a bounded extension with all later absolute
weighted terms at least one half. -/
theorem exists_weilLogShiftBoundedHistory_prefix_large_terms
    (height : WeilLogShiftBoundedHistory) (M : ℕ) :
    ∃ extended : WeilLogShiftBoundedHistory,
      (∀ k : ℕ, k < M → extended k = height k) ∧
      ∀ n : ℕ, M + 2 ≤ n → (1 / 2 : ℝ) ≤ weilLogShiftBoundedHistoryTerm extended n := by
  obtain ⟨lam, hprefix, htail, hlarge⟩ :=
    exists_antipodal_recovery_after_prefix (weilLogShiftBoundedHistoryValues height) M
  have hbound (k : ℕ) : |weilLogShiftRecoveryHistory lam k| ≤ 1 := by
    by_cases hk : k < M
    · change |weilLogShiftRecoveryProbe lam (k + 2)| ≤ 1
      rw [hprefix k hk]
      exact abs_le.mpr (height k).property
    · exact (htail (k + 2) (by omega)).le
  let extended : WeilLogShiftBoundedHistory :=
    fun k => ⟨weilLogShiftRecoveryHistory lam k, abs_le.mp (hbound k)⟩
  refine ⟨extended, ?_, ?_⟩
  · intro k hk
    exact Subtype.ext (hprefix k hk)
  · intro n hn
    change (1 / 2 : ℝ) ≤
      |weilDeviation (weilLogShiftRecoveryInverse (weilLogShiftRecoveryHistory lam)) n| *
        pairedLogKernel (log 2) n
    rw [weilDeviation_recoveryInverse_history]
    exact hlarge n hn

/-- A fixed strict lower bound on some absolute term beyond the chosen cutoff. -/
def weilLogShiftBoundedTailEvent (N : ℕ) : Set WeilLogShiftBoundedHistory :=
  {height | ∃ n : ℕ, N + 2 ≤ n ∧ (1 / 4 : ℝ) < weilLogShiftBoundedHistoryTerm height n}

theorem isOpen_weilLogShiftBoundedTailEvent (N : ℕ) :
    IsOpen (weilLogShiftBoundedTailEvent N) := by
  have hset : weilLogShiftBoundedTailEvent N =
      ⋃ n : ℕ, ⋃ (_ : N + 2 ≤ n),
        {height : WeilLogShiftBoundedHistory |
          (1 / 4 : ℝ) < weilLogShiftBoundedHistoryTerm height n} := by
    ext height
    simp only [weilLogShiftBoundedTailEvent, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hset]
  exact isOpen_iUnion fun n => isOpen_iUnion fun _ =>
    isOpen_lt continuous_const (continuous_weilLogShiftBoundedHistoryTerm n)

theorem dense_weilLogShiftBoundedTailEvent (N : ℕ) :
    Dense (weilLogShiftBoundedTailEvent N) := by
  intro height
  choose extended hprefix hlarge using
    (fun M : ℕ => exists_weilLogShiftBoundedHistory_prefix_large_terms height M)
  have hlim : Tendsto extended atTop (𝓝 height) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => height k) atTop (𝓝 (height k))).congr'
    apply eventually_atTop.mpr
    refine ⟨k + 1, fun M hM => ?_⟩
    exact (hprefix M k (by omega)).symm
  apply mem_closure_of_tendsto hlim
  filter_upwards with M
  refine ⟨M + N + 2, by omega, ?_⟩
  have h := hlarge M (M + N + 2) (by omega)
  linarith only [h]

/-- Persistent absolute weighted terms form a dense residual family in the bounded cube. -/
theorem dense_and_residual_weilLogShiftBoundedTailEvents :
    Dense {height : WeilLogShiftBoundedHistory | ∀ N, height ∈ weilLogShiftBoundedTailEvent N} ∧
      {height : WeilLogShiftBoundedHistory | ∀ N, height ∈ weilLogShiftBoundedTailEvent N} ∈
        residual WeilLogShiftBoundedHistory :=
  GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall
    weilLogShiftBoundedTailEvent isOpen_weilLogShiftBoundedTailEvent
    dense_weilLogShiftBoundedTailEvent

/-- On every bounded history, signed, excess, and deficit summability at log 2
are equivalent. No separate one-sided moment hypothesis is imposed. -/
theorem weilLogShiftBoundedHistory_summability_equivalences (height : WeilLogShiftBoundedHistory) :
    ((Summable fun n => weilDeviation
        (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
          pairedLogKernel (log 2) n) ↔
      Summable (fun n => deviationExcess
        (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
          pairedLogKernel (log 2) n)) ∧
    ((Summable fun n => weilDeviation
        (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
          pairedLogKernel (log 2) n) ↔
      Summable (fun n => deviationDeficit
        (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
          pairedLogKernel (log 2) n)) := by
  let lam := weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)
  by_cases hs : Summable fun n => weilDeviation lam n * pairedLogKernel (log 2) n
  · have he := summable_excess_potential_of_summable_potential hs
    have hd := (summable_potential_iff_deficit_of_local_excess he).mp hs
    exact ⟨⟨fun _ => he, fun _ => hs⟩, ⟨fun _ => hd, fun _ => hs⟩⟩
  · have hbad := nonsummable_excess_deficit_of_bounded_recovery lam
      (weilLogShiftBoundedHistory_probe_bound height) hs
    exact ⟨⟨fun h => False.elim (hs h), fun h => False.elim (hbad.1 h)⟩,
      ⟨fun h => False.elim (hs h), fun h => False.elim (hbad.2 h)⟩⟩

/-- All three moments fail at every shift outside the open log-2 interval. -/
def WeilLogShiftBoundedOuterDivergence (height : WeilLogShiftBoundedHistory) : Prop :=
  ∀ y : ℝ, log 2 ≤ |y| →
    (¬ Summable fun n => weilDeviation
      (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
        pairedLogKernel y n) ∧
    (¬ Summable fun n => deviationExcess
      (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
        pairedLogKernel y n) ∧
    (¬ Summable fun n => deviationDeficit
      (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
        pairedLogKernel y n)

theorem weilLogShiftBoundedOuterDivergence_of_tailEvents (height : WeilLogShiftBoundedHistory)
    (htail : ∀ N, height ∈ weilLogShiftBoundedTailEvent N) :
    WeilLogShiftBoundedOuterDivergence height := by
  let lam := weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)
  have hbad : ¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log 2) n := by
    intro hs
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((tendsto_order.mp hs.norm.tendsto_atTop_zero).2 (1 / 4) (by norm_num))
    obtain ⟨n, hn, hlarge⟩ := htail M
    have hsmall : weilLogShiftBoundedHistoryTerm height n < 1 / 4 := by
      simpa only [weilLogShiftBoundedHistoryTerm, Real.norm_eq_abs, abs_mul,
        abs_of_pos (pairedLogKernel_pos (log 2) n)] using hM n (by omega)
    linarith only [hlarge, hsmall]
  have hiff := weilLogShiftBoundedHistory_summability_equivalences height
  have hexc : ¬ Summable fun n => deviationExcess lam n * pairedLogKernel (log 2) n :=
    fun he => hbad (hiff.1.mpr he)
  have hdef : ¬ Summable fun n => deviationDeficit lam n * pairedLogKernel (log 2) n :=
    fun hd => hbad (hiff.2.mpr hd)
  intro y hy
  have hin : |log (2 : ℝ)| ≤ |y| := by
    simpa only [abs_of_nonneg (log_nonneg (by norm_num : (1 : ℝ) ≤ 2))] using hy
  exact ⟨fun hs => hbad (summable_kernelPotential_of_abs_le hin hs),
    fun hs => hexc (summable_kernelPotential_of_abs_le hin hs),
    fun hs => hdef (summable_kernelPotential_of_abs_le hin hs)⟩

/-- Generic bounded recovery histories have no finite signed or one-sided
moment at log 2 or any larger absolute shift. -/
theorem dense_and_residual_weilLogShiftBoundedOuterDivergence :
    Dense {height : WeilLogShiftBoundedHistory | WeilLogShiftBoundedOuterDivergence height} ∧
      {height : WeilLogShiftBoundedHistory | WeilLogShiftBoundedOuterDivergence height} ∈
        residual WeilLogShiftBoundedHistory := by
  have hsub : {height : WeilLogShiftBoundedHistory | ∀ N, height ∈ weilLogShiftBoundedTailEvent N} ⊆
      {height | WeilLogShiftBoundedOuterDivergence height} :=
    fun height h => weilLogShiftBoundedOuterDivergence_of_tailEvents height h
  have h := dense_and_residual_weilLogShiftBoundedTailEvents
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Any convergent moment at an outer shift is a meagre exception even inside
the bounded cube; the shift and the moment kind may depend on the history. -/
theorem isMeagre_weilLogShiftBounded_some_outer_moment :
    IsMeagre {height : WeilLogShiftBoundedHistory | ∃ y : ℝ, log 2 ≤ |y| ∧
      ((Summable fun n => weilDeviation
        (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
          pairedLogKernel y n) ∨
       (Summable fun n => deviationExcess
        (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
          pairedLogKernel y n) ∨
       (Summable fun n => deviationDeficit
        (weilLogShiftRecoveryInverse (weilLogShiftBoundedHistoryValues height)) n *
          pairedLogKernel y n))} := by
  change _ᶜ ∈ residual WeilLogShiftBoundedHistory
  apply mem_of_superset dense_and_residual_weilLogShiftBoundedOuterDivergence.2
  rintro height hh ⟨y, hy, hs | hs | hs⟩
  · exact (hh y hy).1 hs
  · exact (hh y hy).2.1 hs
  · exact (hh y hy).2.2 hs

end RHTower
