import GaloisForLFunctions.RHTower.WeilLogShiftExponentialPrecision

/-!
# Generic divergence under exponentially shrinking observation errors

For every precision rate 0 ≤ σ < 4−π and every positive error amplitude, a
dense residual subset of unit-ball error parameters produces nowhere bounded
moments around any bounded center. The resulting history errors obey the
prescribed exponential envelope at every coordinate.
-/

open Filter Topology Zeta23 Real
open scoped BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- A strict origin tail excursion within the exponentially constrained error family. -/
def weilLogShiftExponentialTailExcursion (center : ℕ →ᵇ ℝ) (ε σ : ℝ) (hσ : 0 ≤ σ)
    (K N : ℕ) : Set (WeilLogShiftUniformHistoryBall 0 1) :=
  {u | ∃ n : ℕ, N + 2 ≤ n ∧ (K : ℝ) < ‖weilLogShiftRecoveryMoment 0
    (weilLogShiftExponentialPerturbation center ε σ hσ u) n‖}

theorem isOpen_weilLogShiftExponentialTailExcursion (center : ℕ →ᵇ ℝ) (ε σ : ℝ)
    (hσ : 0 ≤ σ) (K N : ℕ) :
    IsOpen (weilLogShiftExponentialTailExcursion center ε σ hσ K N) := by
  have hset : weilLogShiftExponentialTailExcursion center ε σ hσ K N =
      ⋃ n : ℕ, ⋃ (_ : N + 2 ≤ n),
        {u : WeilLogShiftUniformHistoryBall 0 1 | (K : ℝ) < ‖weilLogShiftRecoveryMoment 0
          (weilLogShiftExponentialPerturbation center ε σ hσ u) n‖} := by
    ext u
    simp only [weilLogShiftExponentialTailExcursion, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hset]
  exact isOpen_iUnion fun n => isOpen_iUnion fun _ => isOpen_lt continuous_const
    ((((continuous_weilLogShiftRecoveryMomentBCF 0 n).comp
      (continuous_weilLogShiftExponentialPerturbation center ε σ hσ)).comp
        continuous_subtype_val).norm)

/-- Opposite parameter perturbations still create arbitrarily large moments
when the prescribed exponential precision is below the diagonal growth rate. -/
theorem dense_weilLogShiftExponentialTailExcursion (center : ℕ →ᵇ ℝ) (ε σ : ℝ)
    (hε : 0 < ε) (hσ : 0 ≤ σ) (hrate : σ < 4 - π) (K N : ℕ) :
    Dense (weilLogShiftExponentialTailExcursion center ε σ hσ K N) := by
  apply Metric.dense_iff.mpr
  intro u η hη
  obtain ⟨v, hnear, n, hn, hlarge⟩ := exists_weilLogShiftUniformBall_near_large_affine
    (weilLogShiftExponentialMomentCLM ε σ hσ 0) (weilLogShiftRecoveryMoment 0 center)
    (tendsto_weilLogShiftExponentialMomentCLM_diagonal ε σ hε hσ hrate)
    0 1 zero_lt_one u K N η hη
  refine ⟨v, hnear, n, hn, ?_⟩
  rw [weilLogShiftExponentialPerturbation_moment]
  exact hlarge

/-- Generic unit-ball error parameters obeying a fixed exponential envelope
still yield unbounded absolute terms at every real shift simultaneously. -/
theorem dense_and_residual_weilLogShiftExponential_nowhere_bounded
    (center : ℕ →ᵇ ℝ) (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 ≤ σ) (hrate : σ < 4 - π) :
    Dense {u : WeilLogShiftUniformHistoryBall 0 1 | WeilLogShiftUniformNowhereBounded
      (weilLogShiftExponentialPerturbation center ε σ hσ u)} ∧
      {u : WeilLogShiftUniformHistoryBall 0 1 | WeilLogShiftUniformNowhereBounded
        (weilLogShiftExponentialPerturbation center ε σ hσ u)} ∈
          residual (WeilLogShiftUniformHistoryBall 0 1) := by
  letI : CompleteSpace (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) :=
    Metric.isClosed_closedBall.completeSpace_coe
  have h := GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall
    (fun q : ℕ × ℕ => weilLogShiftExponentialTailExcursion center ε σ hσ q.1 q.2)
    (fun q => isOpen_weilLogShiftExponentialTailExcursion center ε σ hσ q.1 q.2)
    (fun q => dense_weilLogShiftExponentialTailExcursion center ε σ hε hσ hrate q.1 q.2)
  have hsub : {u : WeilLogShiftUniformHistoryBall 0 1 | ∀ q : ℕ × ℕ,
      u ∈ weilLogShiftExponentialTailExcursion center ε σ hσ q.1 q.2} ⊆
      {u | WeilLogShiftUniformNowhereBounded
        (weilLogShiftExponentialPerturbation center ε σ hσ u)} := by
    intro u hu
    apply weilLogShiftUniformNowhereBounded_of_origin
    intro B N
    obtain ⟨K, hK⟩ := exists_nat_gt B
    obtain ⟨n, hn, hlarge⟩ := hu (K, N)
    exact ⟨n, by omega, hK.trans hlarge⟩
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Nowhere signed summability remains generic in the exponentially constrained family. -/
theorem dense_and_residual_weilLogShiftExponential_nowhere_summable
    (center : ℕ →ᵇ ℝ) (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 ≤ σ) (hrate : σ < 4 - π) :
    Dense {u : WeilLogShiftUniformHistoryBall 0 1 | ∀ y : ℝ, ¬ Summable
      (weilLogShiftRecoveryMoment y (weilLogShiftExponentialPerturbation center ε σ hσ u))} ∧
      {u : WeilLogShiftUniformHistoryBall 0 1 | ∀ y : ℝ, ¬ Summable
        (weilLogShiftRecoveryMoment y (weilLogShiftExponentialPerturbation center ε σ hσ u))} ∈
          residual (WeilLogShiftUniformHistoryBall 0 1) := by
  have hsub : {u : WeilLogShiftUniformHistoryBall 0 1 | WeilLogShiftUniformNowhereBounded
      (weilLogShiftExponentialPerturbation center ε σ hσ u)} ⊆
      {u | ∀ y : ℝ, ¬ Summable
        (weilLogShiftRecoveryMoment y (weilLogShiftExponentialPerturbation center ε σ hσ u))} :=
    fun _ hu => weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hu
  have h := dense_and_residual_weilLogShiftExponential_nowhere_bounded center ε σ hε hσ hrate
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Even eventual boundedness at one history-dependent shift is meagre under
the prescribed subcritical exponential precision. -/
theorem isMeagre_weilLogShiftExponential_some_eventually_bounded_moment
    (center : ℕ →ᵇ ℝ) (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 ≤ σ) (hrate : σ < 4 - π) :
    IsMeagre {u : WeilLogShiftUniformHistoryBall 0 1 | ∃ y B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ‖weilLogShiftRecoveryMoment y (weilLogShiftExponentialPerturbation center ε σ hσ u) n‖ ≤ B} := by
  change _ᶜ ∈ residual (WeilLogShiftUniformHistoryBall 0 1)
  apply mem_of_superset
    (dense_and_residual_weilLogShiftExponential_nowhere_bounded center ε σ hε hσ hrate).2
  rintro u hu ⟨y, B, N, hbound⟩
  obtain ⟨n, hn, hlarge⟩ := hu y B N
  exact (not_lt_of_ge (hbound n hn)) hlarge

/-- Signed summability at any real shift is a meagre exception among constrained errors. -/
theorem isMeagre_weilLogShiftExponential_some_summable_moment
    (center : ℕ →ᵇ ℝ) (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 ≤ σ) (hrate : σ < 4 - π) :
    IsMeagre {u : WeilLogShiftUniformHistoryBall 0 1 | ∃ y : ℝ, Summable
      (weilLogShiftRecoveryMoment y (weilLogShiftExponentialPerturbation center ε σ hσ u))} := by
  change _ᶜ ∈ residual (WeilLogShiftUniformHistoryBall 0 1)
  apply mem_of_superset
    (dense_and_residual_weilLogShiftExponential_nowhere_summable center ε σ hε hσ hrate).2
  rintro u hu ⟨y, hs⟩
  exact hu y hs

/-- Arbitrarily small exponentially shrinking errors below rate 4−π can
produce nowhere bounded reconstructed moments around every bounded history. -/
theorem exists_weilLogShiftExponentialPrecision_nowhere_bounded
    (center : ℕ →ᵇ ℝ) (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 ≤ σ) (hrate : σ < 4 - π) :
    ∃ h : ℕ →ᵇ ℝ, (∀ k : ℕ, |h k - center k| ≤ ε * exp (-(σ * (k + 2 : ℕ)))) ∧
      WeilLogShiftUniformNowhereBounded h := by
  let zeroError : WeilLogShiftUniformHistoryBall 0 1 := ⟨0, by simp⟩
  obtain ⟨u, _, hu⟩ := Metric.dense_iff.mp
    (dense_and_residual_weilLogShiftExponential_nowhere_bounded center ε σ hε hσ hrate).1
      zeroError 1 zero_lt_one
  exact ⟨weilLogShiftExponentialPerturbation center ε σ hσ u,
    fun k => weilLogShiftExponentialPerturbation_bound center ε σ hε.le hσ u k, hu⟩

end RHTower
