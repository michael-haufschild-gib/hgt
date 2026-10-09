import GaloisForLFunctions.RHTower.WeilLogShiftArbitraryPrecisionImpulse

/-!
# Generic instability under arbitrary bounded weights

One nonzero sufficiently late weight suffices for generic unboundedness at
every shift. The topology is the supremum topology on the closed unit ball
of error parameters, including when the weights tend to zero.
-/

open Filter Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

/-- A bounded coordinatewise weighted error around a bounded center. -/
def weilLogShiftWeightedPerturbation (center q u : ℕ →ᵇ ℝ) : ℕ →ᵇ ℝ :=
  center + q * u

theorem weilLogShiftWeightedPerturbation_apply (center q u : ℕ →ᵇ ℝ) (j : ℕ) :
    weilLogShiftWeightedPerturbation center q u j = center j + q j * u j := rfl

theorem continuous_weilLogShiftWeightedPerturbation (center q : ℕ →ᵇ ℝ) :
    Continuous (weilLogShiftWeightedPerturbation center q) := by
  exact continuous_const.add (ContinuousLinearMap.mul ℝ (ℕ →ᵇ ℝ) q).continuous

/-- A parameter impulse becomes a physical impulse scaled by its weight. -/
theorem weilLogShiftWeightedPerturbation_impulse (center q u : ℕ →ᵇ ℝ)
    (k : ℕ) (t : ℝ) :
    weilLogShiftWeightedPerturbation center q (u + t • weilLogShiftRecoveryUnitHistory k) =
      weilLogShiftRecoveryImpulseHistory (weilLogShiftWeightedPerturbation center q u)
        k (t * q k) := by
  ext j
  change center j + q j * (u j + t * (if j = k then 1 else 0)) =
    center j + q j * u j + (t * q k) * (if j = k then 1 else 0)
  by_cases hj : j = k
  · subst j
    simp only
    ring
  · simp only [if_neg hj]
    ring

/-- Shrinking a unit-ball parameter leaves room for a nearby impulse of
either sign; the distance bound does not depend on the selected coordinate. -/
private theorem weighted_parameter_room (u : ℕ →ᵇ ℝ) (hu : ‖u‖ ≤ 1)
    (k : ℕ) (δ t : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (ht : |t| ≤ δ) :
    ‖(1 - δ) • u + t • weilLogShiftRecoveryUnitHistory k‖ ≤ 1 ∧
      ‖((1 - δ) • u + t • weilLogShiftRecoveryUnitHistory k) - u‖ ≤ 2 * δ := by
  have he : ‖t • weilLogShiftRecoveryUnitHistory k‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖weilLogShiftRecoveryUnitHistory k‖ ≤ |t| * 1 :=
        mul_le_mul_of_nonneg_left (norm_weilLogShiftRecoveryUnitHistory_le k) (abs_nonneg t)
      _ ≤ δ := by simpa only [mul_one] using ht
  have hb : ‖(1 - δ) • u‖ ≤ 1 - δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hδ1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr hδ1)
  have hd : ‖(-δ) • u‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hδ0]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu hδ0
  constructor
  · exact (norm_add_le _ _).trans (by linarith)
  · have hid : ((1 - δ) • u + t • weilLogShiftRecoveryUnitHistory k) - u =
        (-δ) • u + t • weilLogShiftRecoveryUnitHistory k := by module
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith)

/-- A common native tail threshold works for every center and every bounded
weight having at least one nonzero coordinate beyond that threshold. -/
theorem exists_weilLogShiftWeighted_dense_nowhere_bounded :
    ∃ K : ℕ, ∀ center q : ℕ →ᵇ ℝ, (∃ k : ℕ, K ≤ k ∧ q k ≠ 0) →
      Dense {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
        WeilLogShiftUniformNowhereBounded (weilLogShiftWeightedPerturbation center q u)} := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_two_amplitude_alternative
  refine ⟨K, fun center q ⟨k, hk, hq⟩ => Metric.dense_iff.mpr ?_⟩
  intro u η hη
  let δ : ℝ := min (1 / 2) (η / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hnear : 2 * δ < η := by
    have h := min_le_right (1 / 2 : ℝ) (η / 4)
    change δ ≤ η / 4 at h
    linarith
  have hu : ‖(u : ℕ →ᵇ ℝ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
  have hp := weighted_parameter_room u hu k δ δ hδ.le hδ1
    (by rw [abs_of_pos hδ])
  have hm := weighted_parameter_room u hu k δ (-δ) hδ.le hδ1
    (by rw [abs_neg, abs_of_pos hδ])
  let up : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 :=
    ⟨(1 - δ) • (u : ℕ →ᵇ ℝ) + δ • weilLogShiftRecoveryUnitHistory k,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1⟩
  let um : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 :=
    ⟨(1 - δ) • (u : ℕ →ᵇ ℝ) + (-δ) • weilLogShiftRecoveryUnitHistory k,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using hm.1⟩
  have hne : δ * q k ≠ (-δ) * q k := by
    intro h
    have heq : δ = -δ := (mul_right_cancel₀ hq h)
    linarith
  have halt := hK (weilLogShiftWeightedPerturbation center q ((1 - δ) • (u : ℕ →ᵇ ℝ)))
    k hk (δ * q k) ((-δ) * q k) hne
  rcases halt with hpGood | hmGood
  · refine ⟨up, ?_, ?_⟩
    · change dist (up : ℕ →ᵇ ℝ) (u : ℕ →ᵇ ℝ) < η
      rw [dist_eq_norm]
      exact hp.2.trans_lt hnear
    · change WeilLogShiftUniformNowhereBounded
        (weilLogShiftWeightedPerturbation center q
          ((1 - δ) • (u : ℕ →ᵇ ℝ) + δ • weilLogShiftRecoveryUnitHistory k))
      rwa [weilLogShiftWeightedPerturbation_impulse]
  · refine ⟨um, ?_, ?_⟩
    · change dist (um : ℕ →ᵇ ℝ) (u : ℕ →ᵇ ℝ) < η
      rw [dist_eq_norm]
      exact hm.2.trans_lt hnear
    · change WeilLogShiftUniformNowhereBounded
        (weilLogShiftWeightedPerturbation center q
          ((1 - δ) • (u : ℕ →ᵇ ℝ) + (-δ) • weilLogShiftRecoveryUnitHistory k))
      rwa [weilLogShiftWeightedPerturbation_impulse]

/-- Origin tail excursion set in the closed parameter unit ball. -/
def WeilLogShiftWeightedTailLarge (center q : ℕ →ᵇ ℝ) (B N : ℕ) :
    Set (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) :=
  {u | ∃ n : ℕ, N + 2 ≤ n ∧ (B : ℝ) <
    ‖weilLogShiftRecoveryMoment 0 (weilLogShiftWeightedPerturbation center q u) n‖}

theorem isOpen_weilLogShiftWeightedTailLarge (center q : ℕ →ᵇ ℝ) (B N : ℕ) :
    IsOpen (WeilLogShiftWeightedTailLarge center q B N) := by
  have hset : WeilLogShiftWeightedTailLarge center q B N =
      ⋃ n : ℕ, ⋃ (_ : N + 2 ≤ n),
        {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
          (B : ℝ) < ‖weilLogShiftRecoveryMoment 0
            (weilLogShiftWeightedPerturbation center q u) n‖} := by
    ext u
    simp only [WeilLogShiftWeightedTailLarge, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hset]
  exact isOpen_iUnion fun n => isOpen_iUnion fun _ => isOpen_lt continuous_const
    (((continuous_weilLogShiftRecoveryMomentBCF 0 n).comp
      ((continuous_weilLogShiftWeightedPerturbation center q).comp continuous_subtype_val)).norm)

/-- Arbitrary bounded weights with a nonzero sufficiently late coordinate
give a dense residual set of parameters unbounded at every real shift. -/
theorem exists_weilLogShiftWeighted_dense_residual_nowhere_bounded :
    ∃ K : ℕ, ∀ center q : ℕ →ᵇ ℝ, (∃ k : ℕ, K ≤ k ∧ q k ≠ 0) →
      Dense {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
        WeilLogShiftUniformNowhereBounded (weilLogShiftWeightedPerturbation center q u)} ∧
      {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
        WeilLogShiftUniformNowhereBounded (weilLogShiftWeightedPerturbation center q u)} ∈
        residual (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftWeighted_dense_nowhere_bounded
  refine ⟨K, fun center q hq => ?_⟩
  letI : CompleteSpace (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) :=
    Metric.isClosed_closedBall.completeSpace_coe
  have hdense (B N : ℕ) : Dense (WeilLogShiftWeightedTailLarge center q B N) := by
    apply (hK center q hq).mono
    intro u hu
    exact hu 0 B (N + 2)
  have h := GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall
    (fun p : ℕ × ℕ => WeilLogShiftWeightedTailLarge center q p.1 p.2)
    (fun p => isOpen_weilLogShiftWeightedTailLarge center q p.1 p.2)
    (fun p => hdense p.1 p.2)
  have hsub : {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      ∀ p : ℕ × ℕ, u ∈ WeilLogShiftWeightedTailLarge center q p.1 p.2} ⊆
      {u | WeilLogShiftUniformNowhereBounded (weilLogShiftWeightedPerturbation center q u)} := by
    intro u hu
    apply weilLogShiftUniformNowhereBounded_of_origin
    intro B N
    obtain ⟨B', hB⟩ := exists_nat_gt B
    obtain ⟨n, hn, hlarge⟩ := hu (B', N)
    exact ⟨n, by omega, hB.trans hlarge⟩
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Signed summability fails at every shift for a dense residual set of
parameters under the same single-coordinate nonzero-weight hypothesis. -/
theorem exists_weilLogShiftWeighted_dense_residual_nowhere_summable :
    ∃ K : ℕ, ∀ center q : ℕ →ᵇ ℝ, (∃ k : ℕ, K ≤ k ∧ q k ≠ 0) →
      Dense {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
        ∀ y : ℝ, ¬ Summable
          (weilLogShiftRecoveryMoment y (weilLogShiftWeightedPerturbation center q u))} ∧
      {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
        ∀ y : ℝ, ¬ Summable
          (weilLogShiftRecoveryMoment y (weilLogShiftWeightedPerturbation center q u))} ∈
        residual (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftWeighted_dense_residual_nowhere_bounded
  refine ⟨K, fun center q hq => ?_⟩
  have h := hK center q hq
  have hsub : {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      WeilLogShiftUniformNowhereBounded (weilLogShiftWeightedPerturbation center q u)} ⊆
      {u | ∀ y : ℝ, ¬ Summable
        (weilLogShiftRecoveryMoment y (weilLogShiftWeightedPerturbation center q u))} := by
    intro u hu
    exact weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hu
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- Parameters producing an eventually bounded or summable moment sequence
at even one real shift form meagre exceptional sets. -/
theorem exists_weilLogShiftWeighted_meagre_exceptions :
    ∃ K : ℕ, ∀ center q : ℕ →ᵇ ℝ, (∃ k : ℕ, K ≤ k ∧ q k ≠ 0) →
      IsMeagre {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
        ∃ (y B : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
          ‖weilLogShiftRecoveryMoment y (weilLogShiftWeightedPerturbation center q u) n‖ ≤ B} ∧
      IsMeagre {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
        ∃ y : ℝ, Summable
          (weilLogShiftRecoveryMoment y (weilLogShiftWeightedPerturbation center q u))} := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftWeighted_dense_residual_nowhere_bounded
  refine ⟨K, fun center q hq => ?_⟩
  have h := (hK center q hq).2
  constructor
  · change _ᶜ ∈ residual (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1)
    apply mem_of_superset h
    rintro u hu ⟨y, B, N, hbound⟩
    obtain ⟨n, hn, hlarge⟩ := hu y B N
    exact (not_lt_of_ge (hbound n hn)) hlarge
  · change _ᶜ ∈ residual (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1)
    apply mem_of_superset h
    rintro u hu ⟨y, hs⟩
    exact weilLogShiftUniform_nowhere_summable_of_nowhere_bounded hu y hs

end RHTower
