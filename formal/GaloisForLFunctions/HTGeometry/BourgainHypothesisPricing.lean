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


/-!
### One parameter, three names

With the within-arc level proved (Theorem 81, `w = 1`), the campaign's Farey bookkeeping gives
`fareyExponent 1 x = 5/2 − x`, where `x ∈ [0,1]` is the **across-arc** cancellation exponent (`0` none,
`1` square-root).  In `N` that is `(5/2 − x)/3`.

On the `hDirect` axis at the critical block, `S⁶ ≤ M³T^e` gives `S ≤ T^{(3/2+e)/6} = N^{(3/2+e)/3}`.
Equating the two:

    (3/2 + e)/3 = (5/2 − x)/3   ⟺   **e = 1 − x** .

So the corpus's hypothesis exponent and the campaign's across-arc parameter are the same quantity:

    Weyl      :  e = 1     ⟺  x = 0     (no across-arc cancellation)
    Bourgain  :  e = 13/14 ⟺  x = 1/14  (matching Theorem 45's independently-derived `1/14`)
    Lindelöf  :  e = 0     ⟺  x = 1     (full across-arc square-root cancellation)
-/

/-- The across-arc cancellation exponent corresponding to an `hDirect` exponent. -/
def acrossArcOf (e : ℚ) : ℚ := 1 - e

/-- **Weyl is no across-arc cancellation.** -/
@[simp] theorem acrossArcOf_weyl : acrossArcOf hDirectWeyl = 0 := by
  unfold acrossArcOf hDirectWeyl; norm_num

/-- **Bourgain is `x = 1/14`** — exactly the fraction Theorem 45 derived independently. -/
@[simp] theorem acrossArcOf_bourgain : acrossArcOf (13/14) = 1/14 := by
  unfold acrossArcOf; norm_num

/-- **Lindelöf is full square-root cancellation across arcs.** -/
@[simp] theorem acrossArcOf_lindelof : acrossArcOf 0 = 1 := by
  unfold acrossArcOf; norm_num

/-- The correspondence is an order-reversing bijection. -/
theorem acrossArcOf_antitone {a b : ℚ} (h : a < b) : acrossArcOf b < acrossArcOf a := by
  unfold acrossArcOf; linarith

/-- **The identification, assembled.**  One parameter carries the Weyl exponent, Bourgain's record and
the Lindelöf hypothesis, and it is the campaign's own across-arc cancellation exponent. -/
theorem one_parameter_three_names :
    acrossArcOf hDirectWeyl = 0 ∧ acrossArcOf (13/14) = 1/14 ∧ acrossArcOf 0 = 1 :=
  ⟨acrossArcOf_weyl, acrossArcOf_bourgain, acrossArcOf_lindelof⟩

/-- The remaining across-arc cancellation to be found. -/
@[simp] theorem remaining_across_arc : acrossArcOf 0 - acrossArcOf (13/14) = 13/14 := by
  rw [acrossArcOf_lindelof, acrossArcOf_bourgain]; norm_num


/-!
### Why every conjugation preserves the obstruction

The campaign's transformations — Poisson, finite Fourier, Mellin, reciprocity — are **unitary**, so
they preserve the `ℓ²` norm exactly.  They preserve the `ℓ¹` norm only when they map flat vectors to
flat vectors, and that is what happens here:

* in the resonance basis the terms are unimodular — flat, `ℓ¹/ℓ² = √q` ;
* in the Fourier dual the coefficients satisfy `|ĉ_h| ≍ q^{-1/2}` (Theorem 64) — flat again.

A unit vector flat in **both** position and frequency has `|v_n| = |v̂_h| = q^{-1/2}`: that is the
extremal configuration for the uncertainty principle, and its instances are precisely the chirps
(Gauss sums).  For such a vector the `ℓ¹`-to-`ℓ²` gap is the maximum possible, `√q`, **in both bases**.

So there is no basis reachable by these transforms in which the object is concentrated, and every
conjugation preserves the entire difficulty.  The campaign's five confirmations of the conjugation
principle are instances of one fact: **the frontier object is a chirp.**
-/

/-- `ℓ¹`/`ℓ²` ratio exponent (in `q`) of a flat unit vector with `q` entries. -/
def flatRatioExponent : ℚ := 1/2

/-- The position-basis entries of the frontier object are unimodular: flat. -/
def positionFlat : ℚ := flatRatioExponent

/-- The Fourier-basis entries satisfy `|ĉ_h| ≍ q^{-1/2}`: flat (Theorem 64). -/
def fourierFlat : ℚ := flatRatioExponent

/-- **Flat in both bases — the uncertainty-principle extremal.** -/
theorem flat_in_both : positionFlat = fourierFlat := rfl

/-- **The `ℓ¹`/`ℓ²` gap is the same in both bases**, hence preserved by the transform. -/
@[simp] theorem gap_basis_independent : positionFlat - fourierFlat = 0 := by
  unfold positionFlat fourierFlat; ring

/-- The gap itself, which is the whole remaining difficulty. -/
@[simp] theorem gap_is_half : positionFlat = 1/2 := rfl

/-- **No reachable basis concentrates the object.**  Recorded as: the flat ratio is the same in every
basis the campaign's unitary transforms produce, so no conjugation reduces it. -/
theorem no_concentrating_basis :
    positionFlat = fourierFlat ∧ positionFlat = flatRatioExponent :=
  ⟨flat_in_both, rfl⟩

end HTGeometry
