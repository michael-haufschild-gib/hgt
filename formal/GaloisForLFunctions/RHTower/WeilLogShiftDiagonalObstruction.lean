import GaloisForLFunctions.RHTower.WeilLogShiftFiniteMatrixReceiver

/-!
# Simultaneous diagonal obstruction for bounded recovery histories

Every bounded finite history prefix extends to an antipodal history whose
absolute moments dominate the exact inverse diagonal at every real shift.
Consequently universal bounded-history summability forces diagonal summability.
A dense set of histories simultaneously fails at every shift outside the
diagonal summability domain. No sufficiency of the diagonal condition is claimed.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

private theorem diagonal_le_weighted_deviation (lam : ℕ → ℝ) (k : ℕ)
    (hgap : 1 ≤ weilLogShiftRecoveryWeight (k + 2) (k + 2) *
      |lam (k + 2) - (ArithmeticFunction.vonMangoldt (k + 2) : ℝ)|) (y : ℝ) :
    weilLogShiftRecoveryMomentResponse y (k + 2) k ≤
      |weilDeviation lam (k + 2)| * pairedLogKernel y (k + 2) := by
  have hw := weilLogShiftRecoveryWeight_diagonal_pos (k + 2) (by omega)
  have hr : 0 < sqrt (k + 2 : ℕ) := sqrt_pos.mpr (by positivity)
  have hdelta : 1 / weilLogShiftRecoveryWeight (k + 2) (k + 2) ≤
      |lam (k + 2) - (ArithmeticFunction.vonMangoldt (k + 2) : ℝ)| := by
    apply (div_le_iff₀ hw).mpr
    nlinarith only [hgap]
  have hweighted := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hdelta hr.le) (pairedLogKernel_pos y (k + 2)).le
  rw [weilLogShiftRecoveryMomentResponse_diagonal]
  simp only [weilDeviation, if_pos (show 2 ≤ k + 2 by omega), abs_div, abs_of_pos hr]
  calc
    _ = (1 / weilLogShiftRecoveryWeight (k + 2) (k + 2) / sqrt (k + 2 : ℕ)) *
        pairedLogKernel y (k + 2) := by field_simp [hw.ne', hr.ne']
    _ ≤ _ := hweighted

/-- The diagonal obstruction is already uniformly positive at log 2. -/
theorem half_le_weilLogShiftRecoveryMomentResponse_log_two (k : ℕ) :
    (1 / 2 : ℝ) ≤ weilLogShiftRecoveryMomentResponse (log 2) (k + 2) k := by
  have hw := weilLogShiftRecoveryWeight_diagonal_pos (k + 2) (by omega)
  have hr : 0 < sqrt (k + 2 : ℕ) := sqrt_pos.mpr (by positivity)
  have hbound := mul_le_mul_of_nonneg_right
    (weilLogShiftRecoveryWeight_diagonal_le (k + 2) (by omega)) hr.le
  rw [div_mul_cancel₀ _ hr.ne'] at hbound
  rw [weilLogShiftRecoveryMomentResponse_diagonal]
  apply (le_div_iff₀ (mul_pos hr hw)).mpr
  nlinarith only [hbound]

/-- In particular, the diagonal summability condition fails at log 2. -/
theorem not_summable_weilLogShiftRecoveryDiagonal_log_two :
    ¬ Summable (fun k => weilLogShiftRecoveryMomentResponse (log 2) (k + 2) k) := by
  intro hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hs.tendsto_atTop_zero).2 (1 / 4 : ℝ) (by norm_num))
  have hsmall := hN N le_rfl
  have hlarge := half_le_weilLogShiftRecoveryMomentResponse_log_two N
  linarith only [hsmall, hlarge]

/-- Every bounded prefix admits a single antipodal extension dominating every
weighted inverse diagonal simultaneously, independently of the shift. -/
theorem exists_weilLogShiftBoundedHistory_prefix_diagonal_minorant
    (height : WeilLogShiftBoundedHistory) (M : ℕ) :
    ∃ extended : WeilLogShiftBoundedHistory,
      (∀ k : ℕ, k < M → extended k = height k) ∧
      (∀ k : ℕ, M ≤ k → |weilLogShiftBoundedHistoryValues extended k| = 1) ∧
      ∀ (k : ℕ), M ≤ k → ∀ y : ℝ,
        weilLogShiftRecoveryMomentResponse y (k + 2) k ≤
          ‖weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues extended) (k + 2)‖ := by
  obtain ⟨lam, hprefix, hprobe, hgain⟩ :=
    exists_antipodal_recovery_after_prefix_with_gain (weilLogShiftBoundedHistoryValues height) M
  have hbound (k : ℕ) : |weilLogShiftRecoveryHistory lam k| ≤ 1 := by
    by_cases hk : k < M
    · change |weilLogShiftRecoveryProbe lam (k + 2)| ≤ 1
      rw [hprefix k hk]
      exact abs_le.mpr (height k).property
    · exact (hprobe (k + 2) (by omega)).le
  let extended : WeilLogShiftBoundedHistory :=
    fun k => ⟨weilLogShiftRecoveryHistory lam k, abs_le.mp (hbound k)⟩
  refine ⟨extended, fun k hk => Subtype.ext (hprefix k hk), ?_, ?_⟩
  · intro k hk
    exact hprobe (k + 2) (by omega)
  · intro k hk y
    have hgap : 1 ≤ weilLogShiftRecoveryWeight (k + 2) (k + 2) *
        |lam (k + 2) - (ArithmeticFunction.vonMangoldt (k + 2) : ℝ)| := by
      rw [hgain (k + 2) (by omega)]
      have h := abs_nonneg (weilLogShiftRecoveryProbe
        (weilLogShiftRecoveryPrefix (fun j => ArithmeticFunction.vonMangoldt j) lam (k + 2))
          (k + 2))
      linarith only [h]
    change weilLogShiftRecoveryMomentResponse y (k + 2) k ≤
      ‖weilDeviation (weilLogShiftRecoveryInverse (weilLogShiftRecoveryHistory lam)) (k + 2) *
        pairedLogKernel y (k + 2)‖
    rw [weilDeviation_recoveryInverse_history, Real.norm_eq_abs, abs_mul,
      abs_of_pos (pairedLogKernel_pos y (k + 2))]
    exact diagonal_le_weighted_deviation lam k hgap y

private theorem summable_diagonal_of_eventual_minorant (y : ℝ)
    (height : WeilLogShiftBoundedHistory) (M : ℕ)
    (hminor : ∀ k : ℕ, M ≤ k → weilLogShiftRecoveryMomentResponse y (k + 2) k ≤
      ‖weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height) (k + 2)‖)
    (hs : Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height))) :
    Summable (fun k => weilLogShiftRecoveryMomentResponse y (k + 2) k) := by
  have hshift : Summable (fun k =>
      ‖weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height) (k + 2)‖) :=
    (summable_nat_add_iff 2).mpr hs.norm
  have htail := (summable_nat_add_iff M).mpr hshift
  apply (summable_nat_add_iff M).mp
  exact Summable.of_nonneg_of_le
    (fun k => (weilLogShiftRecoveryMomentResponse_diagonal_pos y (k + M)).le)
    (fun k => hminor (k + M) (by omega)) htail

/-- Universal bounded-history summability forces summability of the exact
positive inverse diagonal. This is a necessary condition, not a converse. -/
theorem weilLogShiftBoundedMomentSummable_diagonal {y : ℝ}
    (hs : WeilLogShiftBoundedMomentSummable y) :
    Summable (fun k => weilLogShiftRecoveryMomentResponse y (k + 2) k) := by
  let zeroHistory : WeilLogShiftBoundedHistory := fun _ => ⟨0, by norm_num⟩
  obtain ⟨height, _, _, hminor⟩ :=
    exists_weilLogShiftBoundedHistory_prefix_diagonal_minorant zeroHistory 0
  exact summable_diagonal_of_eventual_minorant y height 0 (fun k hk => hminor k hk y) (hs height)

/-- One history simultaneously fails at every shift outside the positive
diagonal's summability domain. -/
def WeilLogShiftDiagonalObstruction (height : WeilLogShiftBoundedHistory) : Prop :=
  ∀ y : ℝ, ¬ Summable (fun k => weilLogShiftRecoveryMomentResponse y (k + 2) k) →
    ¬ Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues height))

/-- Arbitrary bounded finite data are compatible with simultaneous failure
at every shift where the inverse diagonal is nonsummable. -/
theorem exists_weilLogShiftBoundedHistory_prefix_diagonal_obstruction
    (height : WeilLogShiftBoundedHistory) (M : ℕ) :
    ∃ extended : WeilLogShiftBoundedHistory,
      (∀ k : ℕ, k < M → extended k = height k) ∧
      WeilLogShiftDiagonalObstruction extended := by
  obtain ⟨extended, hprefix, _, hminor⟩ :=
    exists_weilLogShiftBoundedHistory_prefix_diagonal_minorant height M
  refine ⟨extended, hprefix, fun y hbad hs => ?_⟩
  exact hbad (summable_diagonal_of_eventual_minorant y extended M
    (fun k hk => hminor k hk y) hs)

/-- The same dense family of bounded histories fails at all shifts with
nonsummable inverse diagonal; no countability restriction on shifts is needed. -/
theorem dense_weilLogShiftDiagonalObstruction :
    Dense {height : WeilLogShiftBoundedHistory | WeilLogShiftDiagonalObstruction height} := by
  intro height
  choose extended hprefix hbad using
    (fun M : ℕ => exists_weilLogShiftBoundedHistory_prefix_diagonal_obstruction height M)
  have hlim : Tendsto extended atTop (𝓝 height) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => height k) atTop (𝓝 (height k))).congr'
    apply eventually_atTop.mpr
    refine ⟨k + 1, fun M hM => ?_⟩
    exact (hprefix M k (by omega)).symm
  exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hbad)

end RHTower
