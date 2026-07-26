/-
Weyl's inequality on the Farey arcs, and where the classical exponent `5/6` comes from.

On a coherence block of length `L = N^(1/3)` the critical phase is quadratic, and Weyl's inequality
for `Σ_(n ≤ L) e(α n²)` with `|α - a/q| ≤ 1/q²` gives

    |Σ| ≪ L^(1+ε) (1/q + 1/L + q/L²)^(1/2) .

Writing `q ≍ N^u` with `0 ≤ u ≤ 1/3`, and `L = N^(1/3)`, the dominant term is `1/q`, so the block
bound has exponent

    **1/3 - u/2** ,

which is `1/6 = (1/3)/2` — square-root cancellation on the block — exactly at `u = 1/3`, and trivial
at `u = 0`.

The number of Farey fractions with denominator `≍ N^u` is `≍ N^(2u)`, so the arcs at that scale
contribute in total

    **N^(2u + 1/3 - u/2) = N^(1/3 + 3u/2)** ,

whose maximum over `u ∈ [0, 1/3]` is at `u = 1/3`:  **N^(5/6)** — the classical exponent, recovered
here from a blockwise Weyl computation rather than from the coherence argument.

The Lindelöf target is `N^(1/2)`.  The arcs at scale `u` meet it exactly when `1/3 + 3u/2 ≤ 1/2`, i.e.
`u ≤ 1/9`.  So the arcs with `u ∈ (1/9, 1/3]` — two thirds of the range — require cancellation
**between** arcs, and the total deficit is `N^(5/6 - 1/2) = N^(1/3) = L`, a single factor of the
Farey order.
-/
import GaloisForLFunctions.HTGeometry.LineSegmentAndRecordLattice

namespace HTGeometry

/-! ### The blockwise Weyl exponent -/

/-- Exponent of Weyl's bound on one coherence block whose Farey denominator is `N^u`. -/
def arcBlockExponent (u : ℚ) : ℚ := 1 / 3 - u / 2

/-- **At the largest denominators the block bound is square-root cancellation.** -/
@[simp] theorem arcBlockExponent_at_third : arcBlockExponent (1 / 3) = 1 / 6 := by
  unfold arcBlockExponent; norm_num

/-- **At denominator `O(1)` it is trivial.** -/
@[simp] theorem arcBlockExponent_at_zero : arcBlockExponent 0 = 1 / 3 := by
  unfold arcBlockExponent; norm_num

/-- The block bound improves as the denominator grows. -/
theorem arcBlockExponent_antitone {u u' : ℚ} (h : u < u') :
    arcBlockExponent u' < arcBlockExponent u := by
  unfold arcBlockExponent; linarith

/-! ### Summing over the arcs -/

/-- Exponent of the number of Farey fractions with denominator `≍ N^u`. -/
def arcCountExponent (u : ℚ) : ℚ := 2 * u

/-- Total exponent contributed by the arcs at scale `u`. -/
def arcTotalExponent (u : ℚ) : ℚ := arcCountExponent u + arcBlockExponent u

/-- **It equals `1/3 + 3u/2`.** -/
theorem arcTotalExponent_eq (u : ℚ) : arcTotalExponent u = 1 / 3 + 3 * u / 2 := by
  unfold arcTotalExponent arcCountExponent arcBlockExponent; ring

/-- **The total increases with the scale**, so the largest denominators dominate. -/
theorem arcTotalExponent_mono {u u' : ℚ} (h : u < u') :
    arcTotalExponent u < arcTotalExponent u' := by
  rw [arcTotalExponent_eq, arcTotalExponent_eq]; linarith

/-- **The maximum over the admissible range is the classical exponent `5/6`.** -/
@[simp] theorem arcTotalExponent_at_third : arcTotalExponent (1 / 3) = 5 / 6 := by
  rw [arcTotalExponent_eq]; norm_num

/-- At scale zero the arcs contribute `1/3`. -/
@[simp] theorem arcTotalExponent_at_zero : arcTotalExponent 0 = 1 / 3 := by
  rw [arcTotalExponent_eq]; ring

/-! ### The Lindelöf target and the deficit -/

/-- The Lindelöf target exponent for the whole sum. -/
def lindelofTargetExponent : ℚ := 1 / 2

/-- **The arcs at scale `u` meet the target exactly for `u ≤ 1/9`.** -/
theorem arcs_meet_target_iff (u : ℚ) :
    arcTotalExponent u ≤ lindelofTargetExponent ↔ u ≤ 1 / 9 := by
  rw [arcTotalExponent_eq]
  unfold lindelofTargetExponent
  constructor <;> intro h <;> linarith

/-- **So two thirds of the scale range needs cancellation between arcs.** -/
theorem fraction_needing_across_arc :
    ((1 : ℚ) / 3 - 1 / 9) / (1 / 3) = 2 / 3 := by norm_num

/-- **The total deficit is one factor of the Farey order.** -/
theorem total_deficit :
    arcTotalExponent (1 / 3) - lindelofTargetExponent = 1 / 3 := by
  rw [arcTotalExponent_at_third]; unfold lindelofTargetExponent; norm_num

/-- The Farey order's exponent. -/
def fareyOrderExponent : ℚ := 1 / 3

/-- **And that factor is exactly `L = N^(1/3)`, the Farey order.** -/
theorem deficit_is_farey_order :
    arcTotalExponent (1 / 3) - lindelofTargetExponent = fareyOrderExponent := by
  rw [total_deficit]; unfold fareyOrderExponent; ring

/-! ### Consistency with the campaign's earlier accounting -/

/-- **The blockwise computation reproduces the classical exponent**, which the campaign had obtained
from the coherence argument: incoherent summation over `N^(2/3)` blocks of length `N^(1/3)`. -/
theorem reproduces_classical_exponent :
    arcTotalExponent (1 / 3) = 5 / 6 ∧ lindelofTargetExponent = 1 / 2 ∧
      arcTotalExponent (1 / 3) - lindelofTargetExponent = 1 / 3 :=
  ⟨arcTotalExponent_at_third, rfl, total_deficit⟩

/-- **The within-arc gain is exactly compensated.**  The block bound improves by `u/2` as the
denominator grows, while the arc count grows by `2u`; the net is `+3u/2`, so no choice of scale
recovers the target. -/
theorem within_arc_gain_compensated (u : ℚ) :
    arcCountExponent u - (arcBlockExponent 0 - arcBlockExponent u) = 3 * u / 2 := by
  unfold arcCountExponent arcBlockExponent; ring

/-- **The required saving, in the `q`-sum.**  The arcs' total is `L^(5/2)` where `L = N^(1/3)`; the
target is `L^(3/2)`; so the sum over denominators must save a full factor of `L`. -/
theorem required_q_sum_saving :
    (5 : ℚ) / 2 * (1 / 3) = 5 / 6 ∧ (3 : ℚ) / 2 * (1 / 3) = 1 / 2 ∧
      (5 : ℚ) / 2 - 3 / 2 = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end HTGeometry
