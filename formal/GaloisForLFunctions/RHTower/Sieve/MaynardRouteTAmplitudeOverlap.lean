import GaloisForLFunctions.RHTower.Sieve.MaynardRouteTHighAmplitudeCount
import GaloisForLFunctions.RHTower.Sieve.MaynardWeakLargeValues

/-!
# Route-T amplitude overlap

Route T does not need Maynard--Peck's optimized `5 / 4` gap-moment exponent.  Match the weaker
moment exponent to the fixed long-factor deficit instead.  The elementary amplitude intervals then
overlap.  Turning that interval overlap into a count requires complementary Montgomery estimates
whose height terms dominate; this file records that implication without asserting those hypotheses
for arbitrary factor-length splits.
-/

noncomputable section

namespace RHTower.Sieve

/-- Moment-loss parameter tuned to the fixed long-factor deficit. -/
def routeTGapMomentNu : ℝ :=
  1 / 2 - maynardLongGlobalAmplitudeDeficit / 2

theorem routeTGapMomentNu_pos : 0 < routeTGapMomentNu := by
  dsimp only [routeTGapMomentNu]
  linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]

theorem routeTGapMomentNu_lt_half : routeTGapMomentNu < 1 / 2 := by
  dsimp only [routeTGapMomentNu]
  linarith [maynardLongGlobalAmplitudeDeficit_pos]

theorem routeTGapMomentExponent_lt_three_halves :
    1 + routeTGapMomentNu < 3 / 2 := by
  linarith [routeTGapMomentNu_lt_half]

theorem routeTGapMomentNu_ge_twentyNine_div_oneTwenty :
    29 / 120 ≤ routeTGapMomentNu := by
  dsimp only [routeTGapMomentNu]
  linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]

theorem routeTGapMomentNu_threshold :
    1 / 2 + routeTGapMomentNu =
      1 - maynardLongGlobalAmplitudeDeficit / 2 := by
  dsimp only [routeTGapMomentNu]
  ring

/-- **Formal amplitude overlap.**  Every amplitude is either below the numerical threshold at
which balanced Montgomery would suffice, or strictly above the fixed long-factor boundary.  This
is an interval statement, not an unconditional large-values dichotomy. -/
theorem routeT_balanced_or_endpoint_amplitude (alpha : ℝ) :
    alpha ≤ 1 / 2 + routeTGapMomentNu ∨
      1 - maynardLongGlobalAmplitudeDeficit < alpha := by
  rw [routeTGapMomentNu_threshold]
  by_cases h : alpha ≤ 1 - maynardLongGlobalAmplitudeDeficit / 2
  · exact Or.inl h
  · right
    have hdef : 0 < maynardLongGlobalAmplitudeDeficit :=
      maynardLongGlobalAmplitudeDeficit_pos
    linarith

/-- Balanced Montgomery gives the Route-T first-alternative exponent throughout its half of the
overlap. -/
theorem maynard_balanced_montgomery_routeT_overlap
    {R T M N x alpha beta sigma : ℝ}
    (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hM : 0 < M) (hN : 0 < N) (hx : x = M * N) (hx1 : 1 ≤ x)
    (hscale : x ^ sigma = M ^ alpha * N ^ beta)
    (hRM : R ≤ T * M ^ (1 - 2 * alpha))
    (hRN : R ≤ T * N ^ (1 - 2 * beta))
    (hsigma : sigma ≤ 1 / 2 + routeTGapMomentNu) :
    R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * sigma) := by
  exact maynard_balanced_montgomery_of_split hR hT hM hN hx hx1
    hscale hRM hRN hsigma

end RHTower.Sieve
