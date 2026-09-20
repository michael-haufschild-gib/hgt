import GaloisForLFunctions.RHTower.XiMassTwoRapiditySaddlePolarity

/-!
# Regular diagonal multipliers cannot remove timelike mass saddles

A fixed rapidity multiplier that is nonzero on a diagonal germ cannot enforce the same-order
support required by Route T.  Every sufficiently deep timelike stationary pair enters that germ
while retaining its reversed frequency--rapidity orientation.

Thus a surviving support mechanism must vanish through every diagonal germ, be discontinuous, or
depend nonlocally on the source frequencies.  This result does not supply the alternative:
source-faithful signed cofinal covariance cancellation.
-/

namespace RHTower

noncomputable section

/-- A multiplier nonzero on a fixed diagonal germ retains the literal anti-ordered timelike
stationary pair. -/
theorem xiMassTwoRapidityStationary_survives_diagonal_germ
    {w : ℝ × ℝ → ℂ} {epsilon u h k : ℝ}
    (hw : ∀ t s : ℝ, |t| ≤ epsilon → |s| ≤ epsilon → w (t, s) ≠ 0)
    (hh : 0 < h) (hhk : h < k) (hdeep : 2 * k ≤ u)
    (hsmall : 2 * k / u ≤ epsilon) :
    ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s ∧
      w (t, s) ≠ 0 ∧ |t| ≤ epsilon ∧ |s| ≤ epsilon := by
  have hk : 0 < k := lt_trans hh hhk
  have hu : 0 < u := lt_of_lt_of_le (by linarith) hdeep
  have hku : k < u := by linarith
  have hhu : h < u := hhk.trans hku
  have hdeep_h : 2 * h ≤ u := by linarith
  have hrap_h : timelikeRapidity u h ≤ 2 * h / u :=
    timelikeRapidity_le_two_mul_div hh hdeep_h
  have hrap_k : timelikeRapidity u k ≤ 2 * k / u :=
    timelikeRapidity_le_two_mul_div hk hdeep
  have hrap_h_nonneg : 0 ≤ timelikeRapidity u h := by
    rw [timelikeRapidity]
    exact Real.arsinh_nonneg_iff.mpr (by positivity)
  have hrap_k_nonneg : 0 ≤ timelikeRapidity u k := by
    rw [timelikeRapidity]
    exact Real.arsinh_nonneg_iff.mpr (by positivity)
  have hratio : 2 * h / u ≤ 2 * k / u := by
    exact div_le_div_of_nonneg_right (by linarith) hu.le
  have ht : |-timelikeRapidity u h| ≤ epsilon := by
    rw [abs_neg, abs_of_nonneg hrap_h_nonneg]
    exact hrap_h.trans (hratio.trans hsmall)
  have hs : |-timelikeRapidity u k| ≤ epsilon := by
    rw [abs_neg, abs_of_nonneg hrap_k_nonneg]
    exact hrap_k.trans hsmall
  refine ⟨-timelikeRapidity u h, -timelikeRapidity u k, ?_, hw _ _ ht hs, ht, hs⟩
  exact ⟨(massPhase_timelike_stationary_iff hu hh.le hhu _).mpr rfl,
    (massPhase_timelike_stationary_iff hu hk.le hku _).mpr rfl⟩

end

end RHTower
