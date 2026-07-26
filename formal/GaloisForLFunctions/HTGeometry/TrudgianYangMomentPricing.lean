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
import Mathlib.Tactic.Ring

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


/-!
### What decay rate would be needed, and what is observed

For a geometric tail with ratio `r`, the remaining decrease after a decrement `d` is `d·r/(1-r)`.  The
gap at `A = 15` is `g`, so the trend reaches the record exactly when

    d·r/(1-r) ≥ g   ⟺   r ≥ g/(g+d) .

With `g = 0.0061515` and `d = 0.0013723` this is `r ≥ 0.81766…`.  The observed ratios are
`0.7434` and `0.7345` — **below the requirement, and decreasing.**

The same computation on the *absolute* gaps `M(A) - 13A/84` gives `g = 0.092271`, `d = 0.013062`,
requiring `r ≥ 0.87603…` against observed `0.8074` and `0.7793` — again below, again decreasing.

**Both formulations agree: the published trend is not merely short of the record, it is moving away
from the decay rate that would reach it.**
-/

/-- The decay ratio a geometric tail needs to close a gap `g` given a last decrement `d`. -/
def requiredRatio (g d : ℚ) : ℚ := g / (g + d)

/-- The requirement for the ratio sequence, from the recorded values. -/
def requiredRatioRatios : ℚ := requiredRatio (61515/10000000) (13723/10000000)

/-- **The required ratio exceeds `0.81`.** -/
theorem requiredRatioRatios_gt : (81:ℚ)/100 < requiredRatioRatios := by
  unfold requiredRatioRatios requiredRatio; norm_num

/-- **And is below `0.82`.** -/
theorem requiredRatioRatios_lt : requiredRatioRatios < 82/100 := by
  unfold requiredRatioRatios requiredRatio; norm_num

/-- The two observed ratios, as rationals. -/
def observedRatio1 : ℚ := 7434/10000
def observedRatio2 : ℚ := 7345/10000

/-- **Both observed ratios fall short of the requirement.** -/
theorem observed_below_required :
    observedRatio1 < requiredRatioRatios ∧ observedRatio2 < requiredRatioRatios := by
  constructor
  · unfold observedRatio1 requiredRatioRatios requiredRatio; norm_num
  · unfold observedRatio2 requiredRatioRatios requiredRatio; norm_num

/-- **And the observed ratios are decreasing — moving away from the requirement.** -/
theorem observed_decreasing : observedRatio2 < observedRatio1 := by
  unfold observedRatio1 observedRatio2; norm_num

/-- The shortfall in the decay rate. -/
theorem ratio_shortfall : (7:ℚ)/100 < requiredRatioRatios - observedRatio2 := by
  unfold requiredRatioRatios requiredRatio observedRatio2; norm_num


/-!
### Transporting a moment bound to a single point

Heath-Brown's argument bounds `R·V^{12} ≪ T²` where `V` is a large-value level and `R` the number of
well-spaced points attaining it.  Setting `R = 1` — a single point — gives `V ≪ T^{1/6}`: **Weyl's
exponent, recovered from a moment argument.**

In general a moment bound `∫|ζ|^{2k} ≪ T^{m(k)}` gives, at a single point, `V^{2k} ≪ T^{m(k)}`, i.e.

    **μ(1/2) ≤ m(k)/(2k)** ,

which is exactly the campaign's neutrality law.  So the transport of a mean-value bound to the
pointwise setting *exists* and is the law already in hand; it is not a new bridge.

Checks: `m(2) = 1` gives `1/4` (convexity); `m(6) = 2` gives `1/6` (Weyl).
-/

/-- The pointwise bound obtained by transporting a `2k`-th moment bound `m` to a single point. -/
def neutralityTransport (m k : ℚ) : ℚ := m / (2 * k)

/-- **The fourth moment transports to the convexity bound.** -/
@[simp] theorem transport_fourth : neutralityTransport 1 2 = 1/4 := by
  unfold neutralityTransport; norm_num

/-- **Heath-Brown's twelfth moment transports to Weyl's exponent.** -/
@[simp] theorem transport_twelfth : neutralityTransport 2 6 = 1/6 := by
  unfold neutralityTransport; norm_num

/-- The twelfth moment is a strict improvement on the fourth, under transport. -/
theorem twelfth_beats_fourth : neutralityTransport 2 6 < neutralityTransport 1 2 := by
  rw [transport_twelfth, transport_fourth]; norm_num

/-- **But neither reaches the record.** -/
theorem transports_miss_record :
    (13/84 : ℚ) < neutralityTransport 2 6 ∧ (13/84 : ℚ) < neutralityTransport 1 2 := by
  rw [transport_twelfth, transport_fourth]
  constructor <;> norm_num

/-- The transport of Trudgian–Yang's `M(15) ≤ 2.4137` (i.e. `k = 15/2`). -/
theorem transport_ty15 : neutralityTransport tyM15 (15/2) = tyM15 / 15 := by
  unfold neutralityTransport
  norm_num

/-- **The transport is the neutrality law**: `μ ≤ m/(2k) = M(A)/A` with `A = 2k`. -/
theorem transport_is_neutrality (M A : ℚ) :
    neutralityTransport M (A/2) = M / A := by
  unfold neutralityTransport
  congr 1
  ring

end HTGeometry
