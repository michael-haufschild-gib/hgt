import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthNegativeSchurSheet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthSingularEnvelope
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthNativeSeam
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspExactCompletedC5SeamOrientation

/-!
# Exact completed C5--D1 slope corridor

This file records the exact shared algebraic frontier between completed C5
orientation and the reflected eighth-order D1 curvature.

If `A`, `B`, `C`, `D` are the even logarithmic source jets and `E`, `F`, `G`
the odd ones, then the C5 orientation slope `Ω'` contains the eighth jet `D`.
The exact identity

`A² * D1 + (4*A² - B) * Ω' = R₇`

cancels `D` completely.  Consequently the single two-sided source corridor
`0 < Ω'` and `(4*A²-B)*Ω' < R₇` proves both C5 orientation positivity and D1
positivity.  The corridor is proved unconditionally in a right neighborhood
of the seam.  Its global actual-source version remains the producer target;
the conditional closure theorem below does not assert that missing law.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Seventh-jet reserve left after the exact eighth-jet cancellation between
the reflected D1 polynomial and completed C5 orientation slope. -/
def thetaCuspC5D1SlopeReserve
    (A B C E F G : ℝ) : ℝ :=
  768 * A ^ (8 : ℕ) - 1344 * A ^ (6 : ℕ) * B + 448 * A ^ (4 : ℕ) * B ^ (2 : ℕ) -
    88 * A ^ (2 : ℕ) * B ^ (3 : ℕ) - 4 * B ^ (4 : ℕ) + 56 * A ^ (5 : ℕ) * C -
    2 * A ^ (3 : ℕ) * B * C + 5 * A * B ^ (2 : ℕ) * C - A ^ (2 : ℕ) * C ^ (2 : ℕ) +
    288 * A ^ (3 : ℕ) * B * E ^ (2 : ℕ) - 72 * A * B ^ (2 : ℕ) * E ^ (2 : ℕ) -
    12 * A ^ (2 : ℕ) * C * E ^ (2 : ℕ) + 3 * B * C * E ^ (2 : ℕ) -
    72 * A ^ (4 : ℕ) * E * F + 42 * A ^ (2 : ℕ) * B * E * F -
    6 * B ^ (2 : ℕ) * E * F - 8 * A ^ (3 : ℕ) * F ^ (2 : ℕ) + 2 * A * B * F ^ (2 : ℕ) -
    4 * A ^ (3 : ℕ) * E * G + A * B * E * G

/-- Polynomial form of the completed C5 orientation slope. -/
def thetaCuspC5D1SlopePolynomial
    (A B C D E F G : ℝ) : ℝ :=
  A ^ (2 : ℕ) * D - 5 * A * B * C + 4 * B ^ (3 : ℕ) - 18 * A ^ (3 : ℕ) * C +
      36 * A ^ (2 : ℕ) * B ^ (2 : ℕ) - A * E * G + 6 * B * E * F -
    2 * A * F ^ (2 : ℕ) - 3 * C * E ^ (2 : ℕ) - 18 * A ^ (2 : ℕ) * E * F +
    72 * A * B * E ^ (2 : ℕ)

/-- Exact C5--D1 cancellation.  The right side is independent of the eighth
jet `D`; this is the nontrivial algebraic weld used by the corridor. -/
theorem thetaCuspC5D1SlopeReserve_identity
    (A B C D E F G : ℝ) :
    A ^ (2 : ℕ) * thetaCuspReflectedEighthPolynomial A B C D +
        thetaCuspRankThreeLowerGap A B *
          thetaCuspC5D1SlopePolynomial A B C D E F G =
      thetaCuspC5D1SlopeReserve A B C E F G := by
  unfold thetaCuspReflectedEighthPolynomial thetaCuspRankThreeLowerGap
    thetaCuspC5D1SlopePolynomial thetaCuspC5D1SlopeReserve
  ring

/-- D1 reflected eighth-order polynomial evaluated on exact logarithmic source
jets, before conversion to the positive-half-line reflection notation. -/
def thetaCuspC5D1RankThreeValue (u : ℝ) : ℝ :=
  thetaCuspReflectedEighthPolynomial
    (-iteratedDeriv 2 thetaCuspLogSource u)
    (-iteratedDeriv 4 thetaCuspLogSource u)
    (-iteratedDeriv 6 thetaCuspLogSource u)
    (-iteratedDeriv 8 thetaCuspLogSource u)

/-- Seventh-jet reserve evaluated on the exact completed theta source. -/
def thetaCuspC5D1SlopeReserveAt (u : ℝ) : ℝ :=
  thetaCuspC5D1SlopeReserve
    (-iteratedDeriv 2 thetaCuspLogSource u)
    (-iteratedDeriv 4 thetaCuspLogSource u)
    (-iteratedDeriv 6 thetaCuspLogSource u)
    (-iteratedDeriv 3 thetaCuspLogSource u)
    (-iteratedDeriv 5 thetaCuspLogSource u)
    (-iteratedDeriv 7 thetaCuspLogSource u)

/-- Shared source corridor: positive C5 slope and slope expenditure strictly
below the seventh-jet reserve.  Its two walls imply C5 and D1 respectively. -/
def thetaCuspC5D1SlopeCorridorAt (u : ℝ) : Prop :=
  0 < thetaCuspC5ExactCompletedSeamOrientationSlope u ∧
    thetaCuspRankThreeLowerGap
        (-iteratedDeriv 2 thetaCuspLogSource u)
        (-iteratedDeriv 4 thetaCuspLogSource u) *
        thetaCuspC5ExactCompletedSeamOrientationSlope u <
      thetaCuspC5D1SlopeReserveAt u

/-- Actual-source specialization of the exact eighth-jet cancellation. -/
theorem thetaCuspC5D1SlopeReserveAt_identity (u : ℝ) :
    (-iteratedDeriv 2 thetaCuspLogSource u) ^ (2 : ℕ) *
        thetaCuspC5D1RankThreeValue u +
      thetaCuspRankThreeLowerGap
          (-iteratedDeriv 2 thetaCuspLogSource u)
          (-iteratedDeriv 4 thetaCuspLogSource u) *
        thetaCuspC5ExactCompletedSeamOrientationSlope u =
      thetaCuspC5D1SlopeReserveAt u := by
  simpa only [thetaCuspC5D1RankThreeValue, thetaCuspC5D1SlopeReserveAt,
    thetaCuspC5ExactCompletedSeamOrientationSlope,
    thetaCuspC5D1SlopePolynomial] using
      thetaCuspC5D1SlopeReserve_identity
        (-iteratedDeriv 2 thetaCuspLogSource u)
        (-iteratedDeriv 4 thetaCuspLogSource u)
        (-iteratedDeriv 6 thetaCuspLogSource u)
        (-iteratedDeriv 8 thetaCuspLogSource u)
        (-iteratedDeriv 3 thetaCuspLogSource u)
        (-iteratedDeriv 5 thetaCuspLogSource u)
        (-iteratedDeriv 7 thetaCuspLogSource u)

/-- Upper corridor wall forces strict D1 positivity at that source point. -/
theorem thetaCuspC5D1RankThreeValue_pos_of_corridor
    {u : ℝ} (h : thetaCuspC5D1SlopeCorridorAt u) :
    0 < thetaCuspC5D1RankThreeValue u := by
  have hA : 0 < -iteratedDeriv 2 thetaCuspLogSource u := by
    simpa only [thetaCuspLogCurvature] using thetaCuspLogCurvature_pos u
  have hid := thetaCuspC5D1SlopeReserveAt_identity u
  unfold thetaCuspC5D1SlopeCorridorAt at h
  have hscaled :
      0 < (-iteratedDeriv 2 thetaCuspLogSource u) ^ (2 : ℕ) *
        thetaCuspC5D1RankThreeValue u := by
    linarith
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hA)).mp hscaled

/-- C5 orientation slope is continuous on the full actual theta orbit. -/
theorem continuous_thetaCuspC5ExactCompletedSeamOrientationSlope :
    Continuous thetaCuspC5ExactCompletedSeamOrientationSlope := by
  have hj (n : ℕ) : Continuous (iteratedDeriv n thetaCuspLogSource) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hasDerivAt_iteratedDeriv_thetaCuspLogSource n u).continuousAt
  unfold thetaCuspC5ExactCompletedSeamOrientationSlope
  fun_prop

/-- Exact source-jet D1 value agrees with the reflected positive-half-line D1
curvature for positive source parameter. -/
theorem thetaCuspC5D1RankThreeValue_eq_fullReflection
    {u : ℝ} (hu : 0 < u) :
    thetaCuspC5D1RankThreeValue u =
      thetaCuspFullReflectionEighthHankelCurvature u := by
  unfold thetaCuspC5D1RankThreeValue
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hu,
    iteratedDeriv_four_thetaCuspLogSource_eq_factor hu,
    iteratedDeriv_six_thetaCuspLogSource_eq_full_jets hu,
    iteratedDeriv_eight_thetaCuspLogSource_eq_full_jets hu,
    ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hu,
    ← thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hu]
  unfold thetaCuspFullLogJetSix
    thetaCuspFullLogJetEight thetaCuspFullReflectionEighthHankelCurvature
    thetaCuspFullReflectedLogCurvature thetaCuspFullReflectedLogFourthJet
    thetaCuspFullReflectedLogSixthJet thetaCuspFullReflectedLogEighthJet
    thetaCuspReflectedEighthPolynomial
  ring

/-- A global actual-source corridor makes C5 orientation strictly positive by
integrating the lower slope wall from its zero seam value. -/
theorem thetaCuspC5ExactCompletedSeamOrientation_pos_of_slopeCorridor
    (h : ∀ u : ℝ, 0 < u → thetaCuspC5D1SlopeCorridorAt u) :
    ∀ u : ℝ, 0 < u → 0 < thetaCuspC5ExactCompletedSeamOrientation u := by
  have hmono : StrictMonoOn thetaCuspC5ExactCompletedSeamOrientation (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro u hu
      exact (hasDerivAt_thetaCuspC5ExactCompletedSeamOrientation u).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      rw [(hasDerivAt_thetaCuspC5ExactCompletedSeamOrientation u).deriv]
      exact (h u hu).1
  intro u hu
  rw [← thetaCuspC5ExactCompletedSeamOrientation_zero]
  exact hmono (by simp) (by simp [hu.le]) hu

/-- A global actual-source corridor makes reflected D1 curvature strictly
positive everywhere on the closed positive half-line. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_slopeCorridor
    (h : ∀ u : ℝ, 0 < u → thetaCuspC5D1SlopeCorridorAt u) :
    ∀ u : ℝ, 0 ≤ u → 0 < thetaCuspFullReflectionEighthHankelCurvature u := by
  intro u hu
  rcases hu.eq_or_lt with rfl | hu
  · exact thetaCuspFullReflectionEighthHankelCurvature_zero_pos
  rw [← thetaCuspC5D1RankThreeValue_eq_fullReflection hu]
  exact thetaCuspC5D1RankThreeValue_pos_of_corridor (h u hu)

/-- One global corridor discharges both surviving C5 and D1 sign gates.  This
is a conditional frontier reduction, not a proof of the corridor premise. -/
theorem thetaCuspC5_D1_closed_of_slopeCorridor
    (h : ∀ u : ℝ, 0 < u → thetaCuspC5D1SlopeCorridorAt u) :
    (∀ u : ℝ, 0 < u → 0 < thetaCuspC5ExactCompletedSeamOrientation u) ∧
      (∀ u : ℝ, 0 ≤ u → 0 < thetaCuspFullReflectionEighthHankelCurvature u) :=
  ⟨thetaCuspC5ExactCompletedSeamOrientation_pos_of_slopeCorridor h,
    thetaCuspFullReflectionEighthHankelCurvature_pos_of_slopeCorridor h⟩

/-- The exact completed theta source satisfies the shared C5--D1 corridor on
some right neighborhood of the seam. -/
theorem eventually_right_thetaCuspC5D1SlopeCorridorAt :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), thetaCuspC5D1SlopeCorridorAt u := by
  have hslope0 : 0 < thetaCuspC5ExactCompletedSeamOrientationSlope 0 := by
    rw [thetaCuspC5ExactCompletedSeamOrientationSlope_zero_eq_fixedActionSeamLogValue]
    exact thetaCuspC5FixedActionSeamLogValue_pos
  have hslope : ∀ᶠ u in 𝓝 (0 : ℝ),
      0 < thetaCuspC5ExactCompletedSeamOrientationSlope u :=
    continuous_thetaCuspC5ExactCompletedSeamOrientationSlope.continuousAt.eventually
      (eventually_gt_nhds hslope0)
  have hd1 : ∀ᶠ u in 𝓝 (0 : ℝ),
      0 < thetaCuspFullReflectionEighthHankelCurvature u :=
    continuousAt_thetaCuspFullReflectionEighthHankelCurvature_zero.eventually
      (eventually_gt_nhds thetaCuspFullReflectionEighthHankelCurvature_zero_pos)
  have hslopeRight : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      0 < thetaCuspC5ExactCompletedSeamOrientationSlope u :=
    Filter.Eventually.filter_mono inf_le_left hslope
  have hd1Right : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      0 < thetaCuspFullReflectionEighthHankelCurvature u :=
    Filter.Eventually.filter_mono inf_le_left hd1
  filter_upwards [hslopeRight, hd1Right, self_mem_nhdsWithin] with u hsu hdu hu
  have hupos : 0 < u := hu
  have hrank : 0 < thetaCuspC5D1RankThreeValue u := by
    rw [thetaCuspC5D1RankThreeValue_eq_fullReflection hupos]
    exact hdu
  have hA : 0 < -iteratedDeriv 2 thetaCuspLogSource u := by
    simpa only [thetaCuspLogCurvature] using thetaCuspLogCurvature_pos u
  have hid := thetaCuspC5D1SlopeReserveAt_identity u
  unfold thetaCuspC5D1SlopeCorridorAt
  constructor
  · exact hsu
  · nlinarith [sq_pos_of_pos hA, mul_pos (sq_pos_of_pos hA) hrank]

end

end RHTower
