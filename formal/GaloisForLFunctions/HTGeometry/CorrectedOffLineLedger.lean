/-
The corrected off-line ledger at `σ = 7/10`.

Two corrections, both from checking the exponent database directly.

**The tuning principle is not new.**  "If `(k, ℓ)` is an exponent pair then `μ(ℓ - k) ≤ k`" is
recorded in the database as a corollary.  It is exactly the statement that a pair whose displacement
equals `σ - 1/2` yields `μ(σ) ≤ κ`.

**The bound `65/882` does not improve the record at `7/10`.**  The database's current sharpest bound
on the interval containing `0.7` is the linear function `405/1202 - (227/601)σ`, giving

    **μ(7/10) ≤ 218/3005 = 0.0725457…** ,

which is below both `65/882 = 0.0736961…` and the `3/40 = 0.075` figure used in earlier cycles.

The ledger at `σ = 7/10`, in `252420`ths:

    convexity prediction  `13/140`   = **23439**
    database's bound      `218/3005` = **18312**
    record threshold      `23/420`   = **13823**

    band width  `4/105` = **9616** ,  captured **5127** ,  remaining **4489 = 67²** .

So **53.3 % of the band is already banked**, not the `46.9 %` recorded from the `3/40` figure — the
position on the off-line route is better than the campaign had it, and the remaining gap is
`4489/252420`.

Structurally, the database's piecewise-linear table is the lower convex envelope of the point set
`{(λ - κ, κ)}` over exponent pairs: the tuning correspondence supplies the points, and convexity of
`μ` interpolates between them.
-/
import GaloisForLFunctions.HTGeometry.TunedPairPrinciple

namespace HTGeometry

/-! ### The database's bound at `σ = 7/10` -/

/-- The linear piece of the current sharpest table containing `σ = 0.7`. -/
def dbLinearPiece (σ : ℚ) : ℚ := 405 / 1202 - (227 / 601) * σ

/-- **Its value at `σ = 7/10`.** -/
@[simp] theorem dbLinearPiece_at_seven_tenths : dbLinearPiece (7 / 10) = 218 / 3005 := by
  unfold dbLinearPiece; norm_num

/-- The endpoints of the piece bracket `7/10`. -/
theorem seven_tenths_in_piece : (53141 : ℚ) / 76066 < 7 / 10 ∧ (7 : ℚ) / 10 < 454 / 641 := by
  constructor <;> norm_num

/-- **The database's bound is below the tuned pair's.** -/
theorem db_beats_tuned : dbLinearPiece (7 / 10) < tunedKappa := by
  rw [dbLinearPiece_at_seven_tenths]
  unfold tunedKappa; norm_num

/-- **And below the `3/40` figure used in earlier cycles.** -/
theorem db_beats_three_fortieths : dbLinearPiece (7 / 10) < muSevenTenths := by
  rw [dbLinearPiece_at_seven_tenths]
  unfold muSevenTenths; norm_num

/-- The margin by which the tuned pair is beaten. -/
theorem tuned_shortfall : tunedKappa - dbLinearPiece (7 / 10) = 3049 / 2650410 := by
  rw [dbLinearPiece_at_seven_tenths]
  unfold tunedKappa; norm_num

/-! ### The corrected ledger -/

/-- The three levels at `σ = 7/10`, expressed over the common denominator `252420`. -/
theorem ledger_common_denominator :
    convexityPrediction bourgainTheta (7 / 10) = 23439 / 252420 ∧
      dbLinearPiece (7 / 10) = 18312 / 252420 ∧
      transferThreshold bourgainTheta (7 / 10) = 13823 / 252420 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold convexityPrediction bourgainTheta; norm_num
  · rw [dbLinearPiece_at_seven_tenths]; norm_num
  · unfold transferThreshold bourgainTheta; norm_num

/-- **The band, the captured part and the remainder.** -/
theorem corrected_ledger :
    transferBandWidth bourgainTheta (7 / 10) = 9616 / 252420 ∧
      convexityPrediction bourgainTheta (7 / 10) - dbLinearPiece (7 / 10) = 5127 / 252420 ∧
      dbLinearPiece (7 / 10) - transferThreshold bourgainTheta (7 / 10) = 4489 / 252420 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [transferBandWidth_eq]; unfold bourgainTheta; norm_num
  · rw [dbLinearPiece_at_seven_tenths]
    unfold convexityPrediction bourgainTheta; norm_num
  · rw [dbLinearPiece_at_seven_tenths]
    unfold transferThreshold bourgainTheta; norm_num

/-- The two parts sum to the band. -/
theorem ledger_adds_up : (5127 : ℚ) + 4489 = 9616 := by norm_num

/-- **The remainder is a perfect square, `67²`.** -/
theorem remainder_is_square : (4489 : ℚ) = 67 ^ 2 := by norm_num

/-- **More than half the band is banked**: `5127/9616 > 1/2`. -/
theorem majority_captured : (1 : ℚ) / 2 < 5127 / 9616 := by norm_num

/-- The corrected capture fraction, against the fraction recorded from the `3/40` figure. -/
theorem capture_fraction_corrected :
    capturedFraction < 5127 / 9616 := by
  unfold capturedFraction; norm_num

/-! ### The tuning correspondence, as recorded in the database -/

/-- **The tuning correspondence**: a pair `(κ, λ)` supplies the point `(λ - κ, κ)` of the growth
table.  This is the database's corollary, and the campaign's tuning principle restated. -/
theorem tuning_correspondence {κ lam : ℚ} : TunedTo κ lam (lam - κ) := rfl

/-- The point supplied by the record pair. -/
theorem record_pair_point : bourgainLambda - bourgainKappa = 1 / 2 ∧ bourgainKappa = 13 / 84 := by
  constructor
  · unfold bourgainLambda bourgainKappa; norm_num
  · rfl

/-- The point supplied by its `A`-image. -/
theorem procA_point :
    procA_snd bourgainKappa bourgainLambda - procA_fst bourgainKappa = 139 / 194 ∧
      procA_fst bourgainKappa = 13 / 194 := by
  rw [procA_bourgain.1, procA_bourgain.2]
  constructor <;> norm_num

/-- The point supplied by the tuned pair. -/
theorem tuned_point : tunedLambda - tunedKappa = 7 / 10 ∧ tunedKappa = 65 / 882 := by
  constructor
  · unfold tunedLambda tunedKappa; norm_num
  · rfl

/-- **The database's linear piece is steeper than the campaign's convexity line**, reflecting that it
interpolates between better pairs: slope `-227/601` against `-13/42`. -/
theorem db_slope_steeper : (227 : ℚ) / 601 > 13 / 42 := by norm_num

end HTGeometry
