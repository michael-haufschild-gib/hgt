import GaloisForLFunctions.RHTower.WallThresholdArithmetic
import GaloisForLFunctions.RHTower.WallForcedProfileWindow

/-!
# The frequency threshold of a block

The one-block estimate is organised around the radius

`X_m = max(C₀,2)·e^{max(0,−m)}`,

past which the logarithmic floor of the symbol absorbs the block's position.  Taking the maximum with
`2` costs nothing and makes the threshold exceed one, which every ray estimate assumes — strictly, so
that the reflected Hardy interval on the inward ray needs no appeal to a null set.

Two properties are all that is used downstream: the threshold opens the floor uniformly over the
block, and it is exactly one power of the block weight `e^{max(0,−m)}` — the weight that appears in
the card's `(11)`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The frequency threshold of the block: the radius past which the logarithmic floor of the symbol
absorbs the block's position. -/
def blockThreshold (C₀ m : ℝ) : ℝ := max C₀ 2 * Real.exp (max 0 (-m))

theorem one_lt_blockThreshold (C₀ m : ℝ) : 1 < blockThreshold C₀ m := by
  have h1 : (2 : ℝ) ≤ max C₀ 2 := le_max_right _ _
  have h2 : (1 : ℝ) ≤ Real.exp (max 0 (-m)) := Real.one_le_exp (le_max_left _ _)
  rw [blockThreshold]
  nlinarith

theorem one_le_blockThreshold (C₀ m : ℝ) : 1 ≤ blockThreshold C₀ m :=
  (one_lt_blockThreshold C₀ m).le

theorem blockThreshold_pos (C₀ m : ℝ) : 0 < blockThreshold C₀ m :=
  lt_of_lt_of_le zero_lt_one (one_le_blockThreshold C₀ m)

/-- The threshold is one power of the block weight. -/
theorem sq_blockThreshold (C₀ m : ℝ) :
    blockThreshold C₀ m ^ 2 = max C₀ 2 ^ 2 * Real.exp (2 * max 0 (-m)) := by
  rw [blockThreshold, mul_pow, ← Real.exp_nat_mul]
  norm_num

omit [CompleteSpace X] in
/-- **The threshold opens the floor uniformly in the block.** -/
theorem blockThreshold_floor {T : X →L[ℂ] X} {σ μ₀ C₀ : ℝ}
    (hC₀ : ∀ m L x : ℝ, C₀ * Real.exp (max 0 (-m)) ≤ |x| → m ≤ L → μ₀ ≤ wallFloor T σ x + L)
    {m : ℝ} :
    ∀ x : ℝ, blockThreshold C₀ m ≤ |x| → ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L := by
  intro x hx L hL
  refine hC₀ m L x ?_ hL.1
  refine le_trans ?_ hx
  rw [blockThreshold]
  have h1 : C₀ ≤ max C₀ 2 := le_max_left _ _
  have h2 : (0 : ℝ) < Real.exp (max 0 (-m)) := Real.exp_pos _
  nlinarith

end GaloisForLFunctions.RHTower
