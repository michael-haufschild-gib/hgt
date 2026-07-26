/-
Pricing the corpus's open Bourgain hypothesis at the critical block.

`RHTower/BourgainSpacingExponentArithmetic.bourgain_spacing_endgame` is conditional on three
sixth-power estimates; the first is

    hDirect :  T^{3/7} ≤ M  →  S⁶ ≤ M³ · T^{13/14} .

At the critical block `M = T^{1/2}` — the Lindelöf configuration, where the approximate functional
equation is self-dual — the hypothesis applies (`3/7 < 1/2`) and yields

    S⁶ ≤ T^{3/2} · T^{13/14} = T^{17/7} ,   so   S ≤ T^{17/42} = (T^{1/2})^{17/21} ,

which is exactly Bourgain's block exponent `17/21`, i.e. `μ = 13/84`.

The Lindelöf hypothesis at the same block is `S ≤ T^{1/4} = (T^{1/2})^{1/2}`, i.e. `S⁶ ≤ T^{3/2} = M³`.

**So the Lindelöf hypothesis is `hDirect` with `T^{13/14}` replaced by `T^{ε}`, and `13/14` is the
entire remaining gap.**
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace HTGeometry

/-- Exponent of `T` in the corpus's `hDirect` hypothesis. -/
def hDirectExponent : ℚ := 13/14

/-- The critical block, as an exponent of `T`. -/
def criticalBlockOfT : ℚ := 1/2

/-- Exponent of `T` for `S⁶` delivered by `hDirect` at the critical block: `3·(1/2) + 13/14`. -/
def sixthPowerAtCritical : ℚ := 3 * criticalBlockOfT + hDirectExponent

@[simp] theorem sixthPowerAtCritical_eq : sixthPowerAtCritical = 17/7 := by
  unfold sixthPowerAtCritical criticalBlockOfT hDirectExponent; norm_num

/-- Hence the exponent of `T` for `S` itself. -/
def blockExponentOfT : ℚ := sixthPowerAtCritical / 6

@[simp] theorem blockExponentOfT_eq : blockExponentOfT = 17/42 := by
  unfold blockExponentOfT; rw [sixthPowerAtCritical_eq]; norm_num

/-- Converting to the campaign's block variable `N = T^{1/2}`. -/
def toBlockVariable (e : ℚ) : ℚ := e / criticalBlockOfT

/-- **`hDirect` at the critical block is exactly Bourgain's `17/21`.** -/
@[simp] theorem hDirect_gives_bourgain : toBlockVariable blockExponentOfT = 17/21 := by
  unfold toBlockVariable criticalBlockOfT; rw [blockExponentOfT_eq]; norm_num

/-- And hence exactly `μ = 13/84`. -/
@[simp] theorem hDirect_gives_mu : (toBlockVariable blockExponentOfT - 1/2) / 2 = 13/84 := by
  rw [hDirect_gives_bourgain]; norm_num

/-- The `T`-exponent that the Lindelöf hypothesis would require in `hDirect`. -/
def lindelofHDirectExponent : ℚ := 0

/-- **Lindelöf is `hDirect` with exponent `0`.** -/
theorem lindelof_is_hDirect_at_zero :
    (3 * criticalBlockOfT + lindelofHDirectExponent) / 6 / criticalBlockOfT = 1/2 := by
  unfold criticalBlockOfT lindelofHDirectExponent; norm_num

/-- **The whole remaining gap is the exponent `13/14` in one hypothesis.** -/
@[simp] theorem remaining_gap_in_hDirect :
    hDirectExponent - lindelofHDirectExponent = 13/14 := by
  unfold hDirectExponent lindelofHDirectExponent; norm_num

/-- The hypothesis applies at the critical block, since `3/7 < 1/2`. -/
theorem hDirect_applies_at_critical : (3:ℚ)/7 < criticalBlockOfT := by
  unfold criticalBlockOfT; norm_num

/-- **The identification, assembled.** -/
theorem campaign_meets_corpus :
    toBlockVariable blockExponentOfT = 17/21 ∧
    (3:ℚ)/7 < criticalBlockOfT ∧
    hDirectExponent - lindelofHDirectExponent = 13/14 :=
  ⟨hDirect_gives_bourgain, hDirect_applies_at_critical, remaining_gap_in_hDirect⟩


/-!
### `hDirect` at exponent zero is the exponent-pair conjecture

`hDirect` with `T`-exponent `e` reads `S⁶ ≤ M³·T^e`, i.e. `S ≤ M^{1/2}·T^{e/6}`.  At `e = 0` this is

    **S ≤ M^{1/2}** ,

square-root cancellation for the critical exponential sum, uniformly for `M ≥ T^{3/7}`.  In
exponent-pair language, `S ≪ (Y/M)^κ M^λ` with `Y ≍ T` gives `S ≤ M^{1/2}` exactly at `(κ,λ) = (0,1/2)`
— **the exponent-pair conjecture.**

So the corpus's open hypothesis interpolates between Bourgain's record (`e = 13/14`) and the
exponent-pair conjecture (`e = 0`), and the campaign's Theorem 25 — only one pair with `λ = 1/2` is
known, namely `(1/2,1/2)`, and the `A`-chain's limit *is* the conjecture — prices exactly that
interpolation.
-/

/-- Block exponent (in `M`) delivered by `hDirect` at `T`-exponent `e`, at the critical block. -/
def hDirectBlockExponent (e : ℚ) : ℚ := (3 * criticalBlockOfT + e) / 6 / criticalBlockOfT

/-- At `e = 13/14` this is Bourgain's `17/21`. -/
@[simp] theorem hDirectBlockExponent_bourgain : hDirectBlockExponent (13/14) = 17/21 := by
  unfold hDirectBlockExponent criticalBlockOfT; norm_num

/-- **At `e = 0` it is `1/2` — square-root cancellation, the exponent pair `(0,1/2)`.** -/
@[simp] theorem hDirectBlockExponent_zero : hDirectBlockExponent 0 = 1/2 := by
  unfold hDirectBlockExponent criticalBlockOfT; norm_num

/-- The map from the hypothesis exponent to the block exponent is affine and increasing. -/
theorem hDirectBlockExponent_mono {a b : ℚ} (h : a < b) :
    hDirectBlockExponent a < hDirectBlockExponent b := by
  unfold hDirectBlockExponent criticalBlockOfT
  norm_num
  linarith

/-- The `T`-exponent at which the hypothesis becomes trivial: `S ≤ M`, i.e. block exponent `1`. -/
def hDirectTrivialExponent : ℚ := 3 * criticalBlockOfT

@[simp] theorem hDirectBlockExponent_trivial :
    hDirectBlockExponent hDirectTrivialExponent = 1 := by
  unfold hDirectBlockExponent hDirectTrivialExponent criticalBlockOfT; norm_num

/-- **The three landmarks on one axis.**  The hypothesis exponent `e` runs from `3/2` (trivial) through
`13/14` (Bourgain) to `0` (the exponent-pair conjecture, hence Lindelöf). -/
theorem hDirect_landmarks :
    hDirectBlockExponent hDirectTrivialExponent = 1 ∧
    hDirectBlockExponent (13/14) = 17/21 ∧
    hDirectBlockExponent 0 = 1/2 :=
  ⟨hDirectBlockExponent_trivial, hDirectBlockExponent_bourgain, hDirectBlockExponent_zero⟩

/-- Fraction of the way from trivial to the conjecture that Bourgain's exponent represents. -/
def hDirectProgress : ℚ := (hDirectTrivialExponent - 13/14) / hDirectTrivialExponent

@[simp] theorem hDirectProgress_eq : hDirectProgress = 8/21 := by
  unfold hDirectProgress hDirectTrivialExponent criticalBlockOfT; norm_num


/-!
### The campaign's within-arc bound on the `hDirect` axis, and how progress divides

The campaign's Theorem 81 (within-arc cancellation at every Farey arc, proved) gives `L^{5/2}` at the
critical block, i.e. `S ≤ T^{5/12}` — Weyl's exponent.  On the `hDirect` axis that is `S⁶ ≤ T^{5/2}`
against `M³ = T^{3/2}`, hence `e = 1`.  So

    trivial                       e = 3/2
    Weyl  (= Thm 81, re-proved)   e = 1
    Bourgain                      e = 13/14
    Lindelöf                      e = 0

Of the total distance `3/2`, Bourgain has covered `3/2 − 13/14 = 4/7`, i.e. `8/21`.  Within that:

    Weyl's share            :  (3/2 − 1)/(4/7)   = (1/2)/(4/7)   = **7/8**
    the spacing analysis    :  (1 − 13/14)/(4/7) = (1/14)/(4/7)  = **1/8**

**Weyl's 1921 step accounts for seven-eighths of all progress on this axis; everything from
Bombieri–Iwaniec through Bourgain accounts for one-eighth.**
-/

/-- `hDirect` exponent corresponding to the campaign's within-arc bound (Theorem 81) = Weyl. -/
def hDirectWeyl : ℚ := 1

/-- Distance covered by Bourgain on the `hDirect` axis. -/
def bourgainCovered : ℚ := hDirectTrivialExponent - 13/14

@[simp] theorem bourgainCovered_eq : bourgainCovered = 4/7 := by
  unfold bourgainCovered hDirectTrivialExponent criticalBlockOfT; norm_num

/-- Weyl's share of that distance. -/
def weylShare : ℚ := (hDirectTrivialExponent - hDirectWeyl) / bourgainCovered

/-- The spacing analysis's share. -/
def spacingShare : ℚ := (hDirectWeyl - 13/14) / bourgainCovered

/-- **Weyl accounts for seven-eighths.** -/
@[simp] theorem weylShare_eq : weylShare = 7/8 := by
  unfold weylShare hDirectTrivialExponent hDirectWeyl criticalBlockOfT
  rw [bourgainCovered_eq]; norm_num

/-- **The spacing analysis accounts for one-eighth.** -/
@[simp] theorem spacingShare_eq : spacingShare = 1/8 := by
  unfold spacingShare hDirectWeyl
  rw [bourgainCovered_eq]; norm_num

/-- The two shares exhaust the progress. -/
theorem shares_sum : weylShare + spacingShare = 1 := by
  rw [weylShare_eq, spacingShare_eq]; norm_num

/-- **Weyl's step is seven times the whole spacing analysis.** -/
theorem weyl_seven_times_spacing : weylShare = 7 * spacingShare := by
  rw [weylShare_eq, spacingShare_eq]; norm_num

/-- The within-arc bound sits at `e = 1`, strictly between trivial and Bourgain. -/
theorem weyl_strictly_between :
    13/14 < hDirectWeyl ∧ hDirectWeyl < hDirectTrivialExponent := by
  unfold hDirectWeyl hDirectTrivialExponent criticalBlockOfT
  constructor <;> norm_num

end HTGeometry
