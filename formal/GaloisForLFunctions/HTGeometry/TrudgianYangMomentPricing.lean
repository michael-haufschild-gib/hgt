/-
Pricing the current published moment bounds against the subconvexity record.

The neutrality law `μ(1/2) ≤ M(A)/A`, applied to the moment bounds of Trudgian–Yang
(*Toward optimal exponent pairs*), gives the following.  Their Theorem 2.2 records

    M(13) ≤ 2.1340 ,   M(14) ≤ 2.2720 ,   M(15) ≤ 2.4137 ,

each strictly better than the Hölder extrapolation `M(A) ≤ 2 + (A-12)·13/42` from Heath-Brown's
`M(12) ≤ 2`.  Dividing by `A`:

    M(13)/13 = 0.16415… ,  M(14)/14 = 0.16228… ,  M(15)/15 = 0.16091… ,

a decreasing sequence, still above Bourgain's `13/84 = 0.15476…`.  The moment route therefore
approaches the record without reaching it; the shortfall at `A = 15` is `≈ 0.00615`.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace HTGeometry

/-- Trudgian–Yang's bound on `M(13)`, as a rational. -/
def tyM13 : ℚ := 2134/1000

/-- Their bound on `M(14)`. -/
def tyM14 : ℚ := 2272/1000

/-- Their bound on `M(15)`. -/
def tyM15 : ℚ := 24137/10000

/-- Hölder extrapolation from Heath-Brown's `M(12) ≤ 2` with `μ = 13/84`:
`M(A) ≤ 2 + (A-12)·13/42`. -/
def holderExtrapolation (A : ℚ) : ℚ := 2 + (A - 12) * (13/42)

/-- **Trudgian–Yang beat the Hölder extrapolation at every computed point.** -/
theorem ty_beats_holder :
    tyM13 < holderExtrapolation 13 ∧ tyM14 < holderExtrapolation 14 ∧
    tyM15 < holderExtrapolation 15 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold tyM13 holderExtrapolation; norm_num
  · unfold tyM14 holderExtrapolation; norm_num
  · unfold tyM15 holderExtrapolation; norm_num

/-- The Lindelöf exponent delivered by a moment bound at order `A`, via the neutrality law. -/
def muFromMoment (M A : ℚ) : ℚ := M / A

/-- **The ratios decrease across the computed range.** -/
theorem ty_ratios_decreasing :
    muFromMoment tyM15 15 < muFromMoment tyM14 14 ∧
    muFromMoment tyM14 14 < muFromMoment tyM13 13 := by
  constructor
  · unfold muFromMoment tyM15 tyM14; norm_num
  · unfold muFromMoment tyM14 tyM13; norm_num

/-- **But none reaches the record.** -/
theorem ty_does_not_beat_bourgain :
    (13/84 : ℚ) < muFromMoment tyM15 15 := by
  unfold muFromMoment tyM15; norm_num

/-- The shortfall at `A = 15`. -/
theorem ty_shortfall : muFromMoment tyM15 15 - 13/84 < 7/1000 := by
  unfold muFromMoment tyM15; norm_num

theorem ty_shortfall_positive : (6:ℚ)/1000 < muFromMoment tyM15 15 - 13/84 := by
  unfold muFromMoment tyM15; norm_num

/-- The threshold a moment bound at order `A` must beat: `M(A) < 13A/84`. -/
def momentThreshold (A : ℚ) : ℚ := 13 * A / 84

/-- **The gap narrows with `A` across the computed range.** -/
theorem gap_narrows :
    tyM15 - momentThreshold 15 < tyM14 - momentThreshold 14 ∧
    tyM14 - momentThreshold 14 < tyM13 - momentThreshold 13 := by
  constructor
  · unfold tyM15 tyM14 momentThreshold; norm_num
  · unfold tyM14 tyM13 momentThreshold; norm_num

/-- At `A = 12` the gap is Heath-Brown's, `2 - 13/7 = 1/7`; the computed points lie below it. -/
theorem gap_below_heathBrown :
    tyM13 - momentThreshold 13 < 2 - momentThreshold 12 := by
  unfold tyM13 momentThreshold; norm_num


/-!
### The trend of the published sequence

Including Heath-Brown's `M(12) ≤ 2`, the neutrality ratios and their gaps to `13/84` are

    A = 12 :  2/12      = 0.1666667 ,  gap 0.0119048
    A = 13 :  2.1340/13 = 0.1641538 ,  gap 0.0093920
    A = 14 :  2.2720/14 = 0.1622857 ,  gap 0.0075238
    A = 15 :  2.4137/15 = 0.1609133 ,  gap 0.0061515

The decrements are `-0.0025128, -0.0018682, -0.0013723`, whose successive ratios are `0.743` and
`0.735` — close to geometric.  Extrapolating geometrically with ratio `≈ 0.74`, the remaining decrease
is `0.0013723·0.74/(1-0.74) ≈ 0.0039`, giving a limiting gap of `≈ 0.0022 > 0`.

**On the published trend the moment route approaches `13/84` from above and does not reach it.**  This
is an extrapolation from four points, not a theorem; what is proved below is only the monotonicity and
the near-geometric decay of the recorded gaps.
-/


/-- Gap of the neutrality ratio at `A` to the record, for the recorded bounds. -/
def gapAt12 : ℚ := 2/12 - 13/84
def gapAt13 : ℚ := tyM13/13 - 13/84
def gapAt14 : ℚ := tyM14/14 - 13/84
def gapAt15 : ℚ := tyM15/15 - 13/84

/-- **All four gaps are strictly positive: the moment route is behind the record at every recorded
order.** -/
theorem gaps_positive :
    0 < gapAt12 ∧ 0 < gapAt13 ∧ 0 < gapAt14 ∧ 0 < gapAt15 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold gapAt12; norm_num
  · unfold gapAt13 tyM13; norm_num
  · unfold gapAt14 tyM14; norm_num
  · unfold gapAt15 tyM15; norm_num

/-- **And they decrease strictly.** -/
theorem gaps_decreasing :
    gapAt15 < gapAt14 ∧ gapAt14 < gapAt13 ∧ gapAt13 < gapAt12 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gapAt15 gapAt14 tyM15 tyM14; norm_num
  · unfold gapAt14 gapAt13 tyM14 tyM13; norm_num
  · unfold gapAt13 gapAt12 tyM13; norm_num

/-- The decrements shrink: the decay is sub-linear, consistent with a geometric trend. -/
theorem decrements_shrink :
    gapAt14 - gapAt15 < gapAt13 - gapAt14 ∧ gapAt13 - gapAt14 < gapAt12 - gapAt13 := by
  constructor
  · unfold gapAt15 gapAt14 gapAt13 tyM15 tyM14 tyM13; norm_num
  · unfold gapAt14 gapAt13 gapAt12 tyM14 tyM13; norm_num

/-- **The recorded gap at `A = 15` is between `0.006` and `0.007`.** -/
theorem gapAt15_bracket : (6:ℚ)/1000 < gapAt15 ∧ gapAt15 < 7/1000 := by
  constructor <;> (unfold gapAt15 tyM15; norm_num)

end HTGeometry
