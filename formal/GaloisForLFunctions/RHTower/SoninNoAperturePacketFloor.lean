import GaloisForLFunctions.RHTower.SoninUnboundedSourcePacket

/-!
# The aperture packet channel has no lower floor

The unit-weight source packets drive the aperture curvature trace below every level, so the
curvature channel admits no uniform lower bound at all.

This is strictly stronger than subadditivity along a flag: subadditivity says refinement never
increases the residual trace, which is consistent with a floor; unboundedness says no floor
exists.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap

/-- **No lower floor.**  No constant bounds the aperture curvature trace of unit-weight source
packets from below. -/
theorem not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ (opTrace (soninAperturePacketCurvature s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c) (fun _ => 1))).re := by
  rintro ⟨M, hM⟩
  obtain ⟨s, hs⟩ := exists_soninAperturePacketCurvature_re_opTrace_lt a b c ha hb hab hbc q
    haq hqb (-M)
  rw [neg_neg] at hs
  exact absurd (hM s) (not_le.mpr hs)

end RHTower
