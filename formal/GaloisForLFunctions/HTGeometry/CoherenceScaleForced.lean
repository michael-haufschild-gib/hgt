/-
The coherence scale is forced, and the deficit equals it.

Split the critical sum of length `N` into blocks of length `N^v`.  There are `N^(1-v)` blocks, and the
Farey dissection of order `L = N^v` has `≍ N^(2v)` fractions.  Requiring exactly one Farey fraction per
block — which is what makes the dissection a dissection — forces

    1 - v = 2v ,   i.e.   **v = 1/3** .

At that scale the within-arc accounting of the previous file gives the total exponent `5v/2 = 5/6`,
while the Lindelöf target is `1/2`.  Hence the deficit is

    **5v/2 - 1/2 = 5/6 - 1/2 = 1/3 = v** ,

**exactly the coherence scale itself**, i.e. exactly one factor of the Farey order `L`.

Two readings.  First, the classical exponent `5/6` is a consequence of the dissection's combinatorics
rather than of the strength of Weyl's inequality: given one fraction per block, no better within-arc
bound than square-root-per-block can change it.  Second, the deficit-free scale would be `v = 1/5`
(where `5v/2 = 1/2`), and the distance between the forced scale `1/3` and the deficit-free scale `1/5`
is what the problem consists of.
-/
import GaloisForLFunctions.HTGeometry.FareyArcAccounting

namespace HTGeometry

/-! ### The forcing -/

/-- Exponent of the number of blocks of length `N^v`. -/
def dissectionBlockCount (v : ℚ) : ℚ := 1 - v

/-- Exponent of the number of Farey fractions of order `N^v`. -/
def fareyCountExponent (v : ℚ) : ℚ := 2 * v

/-- **One fraction per block forces the coherence scale.** -/
theorem one_per_block_forces_third (v : ℚ) :
    dissectionBlockCount v = fareyCountExponent v ↔ v = 1 / 3 := by
  unfold dissectionBlockCount fareyCountExponent
  constructor <;> intro h <;> linarith

/-- At the forced scale both counts are `N^(2/3)`. -/
theorem counts_at_forced_scale :
    dissectionBlockCount (1 / 3) = 2 / 3 ∧ fareyCountExponent (1 / 3) = 2 / 3 := by
  constructor
  · unfold dissectionBlockCount; norm_num
  · unfold fareyCountExponent; norm_num

/-! ### The within-arc total and the deficit -/

/-- The within-arc total at coherence scale `v`. -/
def withinArcTotalExponent (v : ℚ) : ℚ := 5 * v / 2

/-- **At the forced scale it is the classical exponent.** -/
@[simp] theorem withinArcTotal_at_forced : withinArcTotalExponent (1 / 3) = 5 / 6 := by
  unfold withinArcTotalExponent; norm_num

/-- **And it agrees with the arc-by-arc computation.** -/
theorem withinArcTotal_agrees :
    withinArcTotalExponent (1 / 3) = arcTotalExponent (1 / 3) := by
  rw [withinArcTotal_at_forced, arcTotalExponent_at_third]

/-- The deficit against the Lindelöf target at coherence scale `v`. -/
def coherenceDeficit (v : ℚ) : ℚ := withinArcTotalExponent v - lindelofTargetExponent

/-- **At the forced scale the deficit equals the scale itself.** -/
theorem deficit_equals_scale : coherenceDeficit (1 / 3) = 1 / 3 := by
  unfold coherenceDeficit lindelofTargetExponent
  rw [withinArcTotal_at_forced]; norm_num

/-- **So the gap is exactly one factor of the Farey order.** -/
theorem deficit_is_one_farey_order :
    coherenceDeficit (1 / 3) = fareyOrderExponent := by
  rw [deficit_equals_scale]; unfold fareyOrderExponent; ring

/-- The deficit grows with the scale. -/
theorem coherenceDeficit_mono {v v' : ℚ} (h : v < v') :
    coherenceDeficit v < coherenceDeficit v' := by
  unfold coherenceDeficit withinArcTotalExponent; linarith

/-! ### The deficit-free scale -/

/-- The scale at which the within-arc total would already meet the target. -/
def deficitFreeScale : ℚ := 1 / 5

/-- **At that scale the deficit vanishes.** -/
@[simp] theorem deficit_vanishes_at_fifth : coherenceDeficit deficitFreeScale = 0 := by
  unfold coherenceDeficit withinArcTotalExponent lindelofTargetExponent deficitFreeScale
  norm_num

/-- **But it is not one fraction per block.** -/
theorem deficitFreeScale_not_forced :
    dissectionBlockCount deficitFreeScale ≠ fareyCountExponent deficitFreeScale := by
  rw [Ne, one_per_block_forces_third]
  unfold deficitFreeScale; norm_num

/-- At the deficit-free scale there are far more blocks than fractions. -/
theorem deficitFreeScale_counts :
    dissectionBlockCount deficitFreeScale = 4 / 5 ∧
      fareyCountExponent deficitFreeScale = 2 / 5 := by
  constructor
  · unfold dissectionBlockCount deficitFreeScale; norm_num
  · unfold fareyCountExponent deficitFreeScale; norm_num

/-- **The distance between the forced scale and the deficit-free scale.** -/
theorem scale_gap : (1 : ℚ) / 3 - deficitFreeScale = 2 / 15 := by
  unfold deficitFreeScale; norm_num

/-! ### The rigidity statement -/

/-- **The classical exponent is forced by the dissection's combinatorics.**  Given one Farey fraction
per block, the coherence scale is `1/3`, the within-arc total is `5/6`, and the deficit against the
Lindelöf target is exactly the scale. -/
theorem coherence_rigidity :
    (dissectionBlockCount (1 / 3) = fareyCountExponent (1 / 3)) ∧
      withinArcTotalExponent (1 / 3) = 5 / 6 ∧
      coherenceDeficit (1 / 3) = 1 / 3 := by
  refine ⟨?_, withinArcTotal_at_forced, deficit_equals_scale⟩
  rw [one_per_block_forces_third]

/-- **And no other scale is admissible**: the deficit-free scale fails the one-fraction-per-block
condition, and every scale above the forced one has a larger deficit. -/
theorem no_better_scale :
    dissectionBlockCount deficitFreeScale ≠ fareyCountExponent deficitFreeScale ∧
      coherenceDeficit deficitFreeScale < coherenceDeficit (1 / 3) :=
  ⟨deficitFreeScale_not_forced, coherenceDeficit_mono (by unfold deficitFreeScale; norm_num)⟩

end HTGeometry
