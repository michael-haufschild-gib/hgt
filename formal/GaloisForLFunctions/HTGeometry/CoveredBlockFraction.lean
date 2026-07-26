/-
How much of the block range carries a nontrivial bound.

The Lindelöf hypothesis is `|Σ_(n ∼ M) n^(-it)| ≪ M^(1/2) t^ε` for every `1 ≤ M ≤ t^(1/2)`.  Writing
`M = t^c`, the requirement at scale `c` is the exponent `c/2`, and the best known estimate — a pair on
the line of symmetry — gives `κ + c/2`.  That beats the trivial bound `c` exactly when

    κ + c/2 < c ,   i.e.   **c > 2κ** .

So the nontrivial range is `(2κ, 1/2]`, a fraction

    **1 - 4κ**

of the whole block range `(0, 1/2]`.  Below `c = 2κ` the trivial bound is still the best available, and
there the deficit is a full square root.

Along the record sequence the covered fraction is

    Weyl `1/6`             →  **1/3      = 0.333333**
    Bombieri–Iwaniec `9/56` →  **5/14     = 0.357143**
    Huxley `32/205`        →  **77/205   = 0.375610**
    Bourgain `13/84`       →  **8/21     = 0.380952**
    corner `0`             →  **1**

so a century has moved the covered fraction by `8/21 - 1/3 = 1/21`, and the Lindelöf hypothesis
requires the remaining `13/21` — **exactly thirteen times as much as has been gained.**
-/
import GaloisForLFunctions.HTGeometry.PowerProductFloor

namespace HTGeometry

/-! ### The nontrivial range -/

/-- The smallest block scale at which a line pair beats the trivial bound. -/
def nontrivialFrom (κ : ℚ) : ℚ := 2 * κ

/-- **The pair beats the trivial bound exactly above `2κ`.** -/
theorem beats_trivial_iff (κ c : ℚ) : blockPairBound κ c < c ↔ nontrivialFrom κ < c := by
  unfold blockPairBound nontrivialFrom
  constructor <;> intro h <;> linarith

/-- The fraction of the block range `(0, 1/2]` carrying a nontrivial bound. -/
def coveredFraction (κ : ℚ) : ℚ := 1 - 4 * κ

/-- **It is the length of `(2κ, 1/2]` divided by `1/2`.** -/
theorem coveredFraction_eq (κ : ℚ) :
    coveredFraction κ = (1 / 2 - nontrivialFrom κ) / (1 / 2) := by
  unfold coveredFraction nontrivialFrom; ring

/-- The covered fraction increases as the record improves. -/
theorem coveredFraction_antitone {κ κ' : ℚ} (h : κ < κ') :
    coveredFraction κ' < coveredFraction κ := by
  unfold coveredFraction; linarith

/-- **At the corner the whole range is covered.** -/
@[simp] theorem coveredFraction_corner : coveredFraction 0 = 1 := by
  unfold coveredFraction; ring

/-! ### The record sequence -/

@[simp] theorem coveredFraction_weyl : coveredFraction weylKappa = 1 / 3 := by
  unfold coveredFraction weylKappa; norm_num

@[simp] theorem coveredFraction_bi : coveredFraction biKappa = 5 / 14 := by
  unfold coveredFraction biKappa; norm_num

@[simp] theorem coveredFraction_huxley : coveredFraction huxleyPairKappa = 77 / 205 := by
  unfold coveredFraction huxleyPairKappa; norm_num

@[simp] theorem coveredFraction_bourgain : coveredFraction bourgainKappa = 8 / 21 := by
  unfold coveredFraction bourgainKappa; norm_num

/-- **The covered fraction grows strictly along the record sequence.** -/
theorem coveredFractions_increasing :
    coveredFraction weylKappa < coveredFraction biKappa ∧
      coveredFraction biKappa < coveredFraction huxleyPairKappa ∧
      coveredFraction huxleyPairKappa < coveredFraction bourgainKappa := by
  rw [coveredFraction_weyl, coveredFraction_bi, coveredFraction_huxley, coveredFraction_bourgain]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### The ledger -/

/-- **The gain since Weyl.** -/
theorem gain_since_weyl :
    coveredFraction bourgainKappa - coveredFraction weylKappa = 1 / 21 := by
  rw [coveredFraction_bourgain, coveredFraction_weyl]; norm_num

/-- **The remainder required by the Lindelöf hypothesis.** -/
theorem remaining_to_lindelof :
    coveredFraction 0 - coveredFraction bourgainKappa = 13 / 21 := by
  rw [coveredFraction_corner, coveredFraction_bourgain]; norm_num

/-- **The remainder is exactly thirteen times the gain.** -/
theorem remaining_is_thirteen_times_gain :
    coveredFraction 0 - coveredFraction bourgainKappa
      = 13 * (coveredFraction bourgainKappa - coveredFraction weylKappa) := by
  rw [remaining_to_lindelof, gain_since_weyl]; norm_num

/-- **Below `13/42` the trivial bound is still the best available**, and the deficit there is a full
square root. -/
theorem trivial_still_best_below {c : ℚ} (h : c < 13 / 42) :
    ¬ (blockPairBound bourgainKappa c < c) := by
  rw [beats_trivial_iff]
  unfold nontrivialFrom bourgainKappa
  linarith

/-- The deficit at an uncovered scale is `c/2`: trivial gives `c`, the requirement is `c/2`. -/
theorem uncovered_deficit (c : ℚ) : c - c / 2 = c / 2 := by ring

/-- **The complete calibration.**  Covered `8/21`; gained since Weyl `1/21`; remaining `13/21`, which
is thirteen times the gain. -/
theorem block_range_ledger :
    coveredFraction bourgainKappa = 8 / 21 ∧
      coveredFraction bourgainKappa - coveredFraction weylKappa = 1 / 21 ∧
      coveredFraction 0 - coveredFraction bourgainKappa = 13 / 21 ∧
      (13 : ℚ) / 21 = 13 * (1 / 21) := by
  refine ⟨coveredFraction_bourgain, gain_since_weyl, remaining_to_lindelof, by norm_num⟩

end HTGeometry
