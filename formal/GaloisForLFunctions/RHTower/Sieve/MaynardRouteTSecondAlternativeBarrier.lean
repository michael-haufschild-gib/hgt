import GaloisForLFunctions.RHTower.Sieve.MaynardRouteTAmplitudeOverlap

/-!
# Route-T second-alternative barrier

For the longest receiver scale `x = T^(19/9)`, every gap-moment exponent strictly below `3/2`
forces Maynard's second count target below one once the amplitude reaches `75/76`.  A nonempty
large-value fibre therefore cannot satisfy that alternative in this range.  This is a structural
sign obstruction, independent of the quality of any large-values estimate.
-/

noncomputable section

namespace RHTower.Sieve

/-- Exact sign-change amplitude for the second Maynard alternative at `mu = 19/9` and the limiting
gap parameter `nu = 1/2`. -/
def routeTSecondAlternativeBarrier : ℝ := 75 / 76

/-- Above `75/76`, every admissible Route-T moment parameter `nu < 1/2` makes the exponent in the
second Maynard alternative strictly negative at the longest receiver scale. -/
theorem routeT_second_alternative_exponent_neg
    {nu sigma : ℝ} (hnu : nu < 1 / 2)
    (hsigma : routeTSecondAlternativeBarrier ≤ sigma) :
    1 + (19 / 9 : ℝ) * (1 + nu - 2 * sigma) < 0 := by
  dsimp only [routeTSecondAlternativeBarrier] at hsigma
  linarith

/-- A nonempty fibre cannot obey a negative-power second-alternative bound at height greater than
one. -/
theorem not_routeT_second_alternative_of_nonempty
    {R T nu sigma : ℝ} (hR : 1 ≤ R) (hT : 1 < T)
    (hnu : nu < 1 / 2)
    (hsigma : routeTSecondAlternativeBarrier ≤ sigma) :
    ¬ R ≤ T ^ (1 + (19 / 9 : ℝ) * (1 + nu - 2 * sigma)) := by
  intro hbound
  have hexp := routeT_second_alternative_exponent_neg hnu hsigma
  have hpow : T ^ (1 + (19 / 9 : ℝ) * (1 + nu - 2 * sigma)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hT hexp
  linarith

/-- The fixed long-factor endpoint begins strictly above the mandatory first-alternative barrier,
so those two facts alone leave a genuine nonempty amplitude strip. -/
theorem routeT_second_alternative_barrier_lt_long_boundary :
    routeTSecondAlternativeBarrier < 1 - maynardLongGlobalAmplitudeDeficit := by
  dsimp only [routeTSecondAlternativeBarrier]
  linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]

/-- In particular, the deficit-matched parameter already has a negative second-alternative
exponent at the fixed long-factor boundary. -/
theorem routeT_matched_second_alternative_exponent_neg_at_long_boundary :
    1 + (19 / 9 : ℝ) *
      (1 + routeTGapMomentNu - 2 * (1 - maynardLongGlobalAmplitudeDeficit)) < 0 := by
  dsimp only [routeTGapMomentNu]
  linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]

end RHTower.Sieve
