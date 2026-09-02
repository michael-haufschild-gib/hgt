import GaloisForLFunctions.RHTower.ThetaCuspExactCompletedC5D1SlopeCorridor

/-!
# Exact circularity of the completed C5--D1 slope corridor

The proposed upper corridor wall does not reduce the TCD rank-three burden.  On the actual
positive theta orbit, the reserve identity and strict source curvature make that wall equivalent
to native `D1 > 0`.  Consequently the full corridor is exactly the conjunction of positive C5
slope and positive native D1, pointwise and globally.

This kills the corridor as an independent shared producer.  Its positive survivor is a sharp
classification: a genuine common C5--TCD mechanism must control source dynamics not algebraically
equivalent to either target sign.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- On the actual positive source orbit, the C5--D1 corridor is exactly the conjunction of its
C5 slope target and native TCD `D1` target.  In particular its upper wall has no independent
content beyond `D1 > 0`. -/
theorem thetaCuspC5D1SlopeCorridorAt_iff_slope_and_nativeD1
    {u : ℝ} (hu : 0 < u) :
    thetaCuspC5D1SlopeCorridorAt u ↔
      0 < thetaCuspC5ExactCompletedSeamOrientationSlope u ∧
        0 < thetaCuspFullReflectionEighthHankelCurvature u := by
  have hA : 0 < -iteratedDeriv 2 thetaCuspLogSource u := by
    simpa only [thetaCuspLogCurvature] using thetaCuspLogCurvature_pos u
  have hid := thetaCuspC5D1SlopeReserveAt_identity u
  rw [← thetaCuspC5D1RankThreeValue_eq_fullReflection hu]
  unfold thetaCuspC5D1SlopeCorridorAt
  constructor
  · rintro ⟨hslope, hupper⟩
    refine ⟨hslope, ?_⟩
    nlinarith [sq_pos_of_pos hA]
  · rintro ⟨hslope, hd1⟩
    refine ⟨hslope, ?_⟩
    nlinarith [sq_pos_of_pos hA]

/-- Global no-go classification.  Requiring the completed C5--D1 corridor everywhere is exactly
requiring positive C5 slope everywhere together with the full native TCD `D1` theorem, including
the already strict modular seam. -/
theorem every_thetaCuspC5D1SlopeCorridor_iff_c5Slope_and_nativeD1 :
    (∀ u : ℝ, 0 < u → thetaCuspC5D1SlopeCorridorAt u) ↔
      (∀ u : ℝ, 0 < u →
        0 < thetaCuspC5ExactCompletedSeamOrientationSlope u) ∧
      (∀ u : ℝ, 0 ≤ u →
        0 < thetaCuspFullReflectionEighthHankelCurvature u) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u hu
      exact (thetaCuspC5D1SlopeCorridorAt_iff_slope_and_nativeD1 hu).mp (h u hu) |>.1
    · intro u hu
      rcases hu.eq_or_lt with rfl | hu
      · exact thetaCuspFullReflectionEighthHankelCurvature_zero_pos
      · exact (thetaCuspC5D1SlopeCorridorAt_iff_slope_and_nativeD1 hu).mp (h u hu) |>.2
  · rintro ⟨hslope, hd1⟩ u hu
    exact (thetaCuspC5D1SlopeCorridorAt_iff_slope_and_nativeD1 hu).mpr
      ⟨hslope u hu, hd1 u hu.le⟩

end

end RHTower
