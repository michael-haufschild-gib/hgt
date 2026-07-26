/-
The order at which the moment route crosses the record, and a near-miss that had to be discarded.

The slope identity `lim M(A)/A = μ(1/2)` guarantees that the moment ratios eventually fall below any
record.  This file measures how far the published data is from that crossing.

**The gap in the ratio.**  The best published ratio is `M(15)/15 = 24137/150000`, against the record
`13/84`.  Their difference is `6459/1050000`, and multiplying by the order `15` recovers exactly the
exceptional-set residual `6459/70000` of the previous file — the two measurements are the same
quantity seen at different scales.

**The sixteenth moment.**  Emptying the exceptional set at order `16` requires `M(16) ≤ 52/21`.  The
published increments are `M(13)-M(12) = 0.1340`, `M(14)-M(13) = 0.1380`, `M(15)-M(14) = 0.1417`; the
next on trend is about `0.1449`, giving `M(16) ≈ 12793/5000 = 2.5586`.  That exceeds the requirement
by `8653/105000 ≈ 0.0824`, about `57 %` of one increment.

**The near-miss.**  Convexity of the true moment function together with published *values* would give
`μ(1/2) ≥ M(15) - M(14) = 0.1417 > 0`, refuting the Lindelöf hypothesis.  The argument is invalid:
the published `M(A)` are **upper bounds**, not values, and secant slopes of upper bounds carry no
information about the true function's slopes.  Recorded here so the step is not attempted again.
-/
import GaloisForLFunctions.HTGeometry.MomentSlopeIdentity

namespace HTGeometry

/-! ### The gap in the ratio -/

/-- The best published neutrality ratio. -/
def bestPublishedRatio : ℚ := 24137 / 150000

/-- It is `M(15)/15`. -/
theorem bestPublishedRatio_eq : bestPublishedRatio = muFromMoment tyM15 15 := by
  unfold bestPublishedRatio muFromMoment tyM15; norm_num

/-- **The moment route's gap to the record, in the ratio.** -/
theorem moment_ratio_gap : bestPublishedRatio - bourgainTheta = 6459 / 1050000 := by
  unfold bestPublishedRatio bourgainTheta; norm_num

/-- **Multiplying by the order recovers the exceptional-set residual.** -/
theorem gap_times_order :
    15 * (bestPublishedRatio - bourgainTheta) = exceptionalExponent tyM15 15 bourgainTheta := by
  rw [moment_ratio_gap, residual_fifteenth]; norm_num

/-- The gap is between `0.006` and `0.0062`. -/
theorem moment_ratio_gap_bracket :
    (6 : ℚ) / 1000 < bestPublishedRatio - bourgainTheta ∧
      bestPublishedRatio - bourgainTheta < 62 / 10000 := by
  rw [moment_ratio_gap]
  constructor <;> norm_num

/-! ### The sixteenth moment -/

/-- The moment bound at order `16` that would match the record. -/
def requiredSixteenth : ℚ := 52 / 21

/-- **It is `16·13/84`.** -/
theorem requiredSixteenth_eq : requiredSixteenth = 16 * bourgainTheta := by
  unfold requiredSixteenth bourgainTheta; norm_num

/-- **And it empties the exceptional set at order `16`.** -/
theorem requiredSixteenth_empties :
    exceptionalExponent requiredSixteenth 16 bourgainTheta = 0 := by
  unfold exceptionalExponent requiredSixteenth bourgainTheta; norm_num

/-- The published increments of the moment bounds. -/
theorem published_increments :
    tyM13 - 2 = 67 / 500 ∧ tyM14 - tyM13 = 69 / 500 ∧ tyM15 - tyM14 = 1417 / 10000 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold tyM13; norm_num
  · unfold tyM14 tyM13; norm_num
  · unfold tyM15 tyM14; norm_num

/-- The increments increase. -/
theorem increments_increasing :
    tyM13 - 2 < tyM14 - tyM13 ∧ tyM14 - tyM13 < tyM15 - tyM14 := by
  rw [published_increments.1, published_increments.2.1, published_increments.2.2]
  constructor <;> norm_num

/-- The value at order `16` predicted by continuing the increment trend. -/
def trendSixteenth : ℚ := 12793 / 5000

/-- **The trend value exceeds the requirement.** -/
theorem trend_exceeds_requirement : requiredSixteenth < trendSixteenth := by
  unfold requiredSixteenth trendSixteenth; norm_num

/-- **By `8653/105000`.** -/
theorem trend_excess : trendSixteenth - requiredSixteenth = 8653 / 105000 := by
  unfold trendSixteenth requiredSixteenth; norm_num

/-- That excess is under sixty percent of the last published increment. -/
theorem excess_fraction_of_increment :
    trendSixteenth - requiredSixteenth < (6 / 10 : ℚ) * (tyM15 - tyM14) := by
  rw [trend_excess, published_increments.2.2]; norm_num

/-- Hölder from the fifteenth gives a much weaker value at order `16`. -/
def holderSixteenth : ℚ := tyM15 + 13 / 42

/-- **It exceeds the requirement by `7411/30000`.** -/
theorem holder_excess : holderSixteenth - requiredSixteenth = 7411 / 30000 := by
  unfold holderSixteenth requiredSixteenth tyM15; norm_num

/-- The trend is a genuine improvement on Hölder at order `16`. -/
theorem trend_beats_holder : trendSixteenth < holderSixteenth := by
  unfold trendSixteenth holderSixteenth tyM15; norm_num

/-! ### The discarded near-miss

Convexity of the true moment function would give `μ(1/2) ≥ M(15) - M(14)` if the published values
were exact.  The conclusion `μ(1/2) ≥ 1417/10000 > 0` would refute the Lindelöf hypothesis.  It does
not follow: the published quantities are upper bounds. -/

/-- The value the invalid argument would have produced. -/
def discardedLowerBound : ℚ := tyM15 - tyM14

/-- **It is positive**, which is why the step had to be examined. -/
theorem discardedLowerBound_pos : 0 < discardedLowerBound := by
  unfold discardedLowerBound tyM15 tyM14; norm_num

/-- **And it lies below the record**, so even as a heuristic it is consistent with `13/84` — the
inconsistency is with the Lindelöf hypothesis, not with the record. -/
theorem discardedLowerBound_below_record : discardedLowerBound < bourgainTheta := by
  unfold discardedLowerBound tyM15 tyM14 bourgainTheta; norm_num

/-- **The reason it fails, recorded as an inequality**: an upper bound `M` for the true `m` gives no
lower bound on any secant of `m`.  Formally, `m ≤ M` pointwise is compatible with `m` constant. -/
theorem upper_bounds_give_no_secant (m : ℚ → ℚ)
    (hconst : ∀ A, m A = 1) (A B : ℚ) : m B - m A = 0 := by
  rw [hconst A, hconst B]; ring

end HTGeometry
