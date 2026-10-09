import GaloisForLFunctions.RHTower.WeilLogShiftPrecisionFeasibleSet

/-!
# Genericity in the actual precision-constrained history space

The inherited supremum topology on all feasible bounded histories supports
generic nowhere boundedness and signed nonsummability. One sufficiently
late positive tolerance suffices, even if every other tolerance is zero or
the profile is unbounded. All-positive profiles allow every exact prefix.
-/

open Filter Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

/-- An origin tail excursion inside the actual feasible history set. -/
def WeilLogShiftPrecisionFeasibleTailLarge (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ)
    (M B N : ℕ) : Set (WeilLogShiftPrecisionHistory center ε M) :=
  {h | ∃ n : ℕ, N + 2 ≤ n ∧ (B : ℝ) < ‖weilLogShiftRecoveryMoment 0 h n‖}

theorem isOpen_weilLogShiftPrecisionFeasibleTailLarge (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (M B N : ℕ) :
    IsOpen (WeilLogShiftPrecisionFeasibleTailLarge center ε M B N) := by
  have hset : WeilLogShiftPrecisionFeasibleTailLarge center ε M B N =
      ⋃ n : ℕ, ⋃ (_ : N + 2 ≤ n),
        {h : WeilLogShiftPrecisionHistory center ε M |
          (B : ℝ) < ‖weilLogShiftRecoveryMoment 0 h n‖} := by
    ext h
    simp only [WeilLogShiftPrecisionFeasibleTailLarge, Set.mem_setOf_eq,
      Set.mem_iUnion, exists_prop]
  rw [hset]
  exact isOpen_iUnion fun n => isOpen_iUnion fun _ => isOpen_lt continuous_const
    (((continuous_weilLogShiftRecoveryMomentBCF 0 n).comp continuous_subtype_val).norm)

/-- A nonzero tolerance at one native late coordinate gives dense residual
nowhere boundedness in the actual feasible history set, with its supremum metric. -/
theorem exists_weilLogShiftPrecisionFeasible_dense_residual_nowhere_bounded :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (M : ℕ),
      (∃ k : ℕ, K ≤ k ∧ M ≤ k ∧ 0 < ε k) →
        Dense {h : WeilLogShiftPrecisionHistory center ε M |
          WeilLogShiftUniformNowhereBounded h} ∧
        {h : WeilLogShiftPrecisionHistory center ε M | WeilLogShiftUniformNowhereBounded h} ∈
          residual (WeilLogShiftPrecisionHistory center ε M) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftPrecisionFeasible_dense_nowhere_bounded
  refine ⟨K, fun center ε M hk => ?_⟩
  letI : CompleteSpace (WeilLogShiftPrecisionHistory center ε M) :=
    (isClosed_weilLogShiftPrecisionFeasibleSet center ε M).completeSpace_coe
  have hdense (B N : ℕ) : Dense (WeilLogShiftPrecisionFeasibleTailLarge center ε M B N) := by
    apply (hK center ε M hk).mono
    intro h hh
    exact hh 0 B (N + 2)
  have h := GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall
    (fun p : ℕ × ℕ => WeilLogShiftPrecisionFeasibleTailLarge center ε M p.1 p.2)
    (fun p => isOpen_weilLogShiftPrecisionFeasibleTailLarge center ε M p.1 p.2)
    (fun p => hdense p.1 p.2)
  have hsub : {h : WeilLogShiftPrecisionHistory center ε M |
      ∀ p : ℕ × ℕ, h ∈ WeilLogShiftPrecisionFeasibleTailLarge center ε M p.1 p.2} ⊆
      {h | WeilLogShiftUniformNowhereBounded h} := by
    intro h hh
    apply weilLogShiftUniformNowhereBounded_of_origin
    intro B N
    obtain ⟨B', hB⟩ := exists_nat_gt B
    obtain ⟨n, hn, hlarge⟩ := hh (B', N)
    exact ⟨n, by omega, hB.trans hlarge⟩
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Every strictly positive profile gives generic nowhere boundedness
among all feasible bounded histories, preserving any finite exact prefix. -/
theorem weilLogShiftPrecisionFeasible_positive_dense_residual_nowhere_bounded
    (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) :
    Dense {h : WeilLogShiftPrecisionHistory center ε M | WeilLogShiftUniformNowhereBounded h} ∧
    {h : WeilLogShiftPrecisionHistory center ε M | WeilLogShiftUniformNowhereBounded h} ∈
      residual (WeilLogShiftPrecisionHistory center ε M) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftPrecisionFeasible_dense_residual_nowhere_bounded
  exact hK center ε M ⟨max K M, le_max_left _ _, le_max_right _ _, hε _⟩

/-- Generic failure of signed summability in the actual feasible history set. -/
theorem exists_weilLogShiftPrecisionFeasible_dense_residual_nowhere_summable :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (M : ℕ),
      (∃ k : ℕ, K ≤ k ∧ M ≤ k ∧ 0 < ε k) →
        Dense {h : WeilLogShiftPrecisionHistory center ε M |
          ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y h)} ∧
        {h : WeilLogShiftPrecisionHistory center ε M |
          ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y h)} ∈
          residual (WeilLogShiftPrecisionHistory center ε M) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftPrecisionFeasible_dense_residual_nowhere_bounded
  refine ⟨K, fun center ε M hk => ?_⟩
  have h := hK center ε M hk
  have hsub : {h : WeilLogShiftPrecisionHistory center ε M | WeilLogShiftUniformNowhereBounded h} ⊆
      {h | ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y h)} := by
    intro h hh
    exact weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hh
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Arbitrary positive precision leaves signed nonsummability generic in
the inherited supremum topology of the full feasible set. -/
theorem weilLogShiftPrecisionFeasible_positive_dense_residual_nowhere_summable
    (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) :
    Dense {h : WeilLogShiftPrecisionHistory center ε M |
      ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y h)} ∧
    {h : WeilLogShiftPrecisionHistory center ε M |
      ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y h)} ∈
      residual (WeilLogShiftPrecisionHistory center ε M) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftPrecisionFeasible_dense_residual_nowhere_summable
  exact hK center ε M ⟨max K M, le_max_left _ _, le_max_right _ _, hε _⟩

/-- Even one eventually bounded or summable shift is a meagre exception
among actual feasible histories, without restricting the tolerance decay rate. -/
theorem exists_weilLogShiftPrecisionFeasible_meagre_exceptions :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (M : ℕ),
      (∃ k : ℕ, K ≤ k ∧ M ≤ k ∧ 0 < ε k) →
        IsMeagre {h : WeilLogShiftPrecisionHistory center ε M |
          ∃ (y B : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n → ‖weilLogShiftRecoveryMoment y h n‖ ≤ B} ∧
        IsMeagre {h : WeilLogShiftPrecisionHistory center ε M |
          ∃ y : ℝ, Summable (weilLogShiftRecoveryMoment y h)} := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftPrecisionFeasible_dense_residual_nowhere_bounded
  refine ⟨K, fun center ε M hk => ?_⟩
  have h := (hK center ε M hk).2
  constructor
  · change _ᶜ ∈ residual (WeilLogShiftPrecisionHistory center ε M)
    apply mem_of_superset h
    rintro h hh ⟨y, B, N, hbound⟩
    obtain ⟨n, hn, hlarge⟩ := hh y B N
    exact (not_lt_of_ge (hbound n hn)) hlarge
  · change _ᶜ ∈ residual (WeilLogShiftPrecisionHistory center ε M)
    apply mem_of_superset h
    rintro h hh ⟨y, hs⟩
    exact weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hh y hs

/-- At arbitrary strictly positive precision, the bounded or summable
exceptions are meagre in the full feasible-history topology. -/
theorem weilLogShiftPrecisionFeasible_positive_meagre_exceptions
    (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) :
    IsMeagre {h : WeilLogShiftPrecisionHistory center ε M |
      ∃ (y B : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n → ‖weilLogShiftRecoveryMoment y h n‖ ≤ B} ∧
    IsMeagre {h : WeilLogShiftPrecisionHistory center ε M |
      ∃ y : ℝ, Summable (weilLogShiftRecoveryMoment y h)} := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftPrecisionFeasible_meagre_exceptions
  exact hK center ε M ⟨max K M, le_max_left _ _, le_max_right _ _, hε _⟩

end RHTower
