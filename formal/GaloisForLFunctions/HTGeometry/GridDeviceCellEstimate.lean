import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The cell estimate of the grid device, and why its two bounds coincide

The grid cancellation device counts zeros of a continuous `f` on a window by comparing the absolute
mass `L ≤ ∫|f|` with the summed cell cancellation `Bsum = ∑_j |∫_{I_j} f|`.  Per cell,
Cauchy–Schwarz gives `|∫_{I_j} f|² ≤ H ∫_{I_j} f²`, and Cauchy–Schwarz over the cells then gives

```text
Bsum²  ≤  (#cells · H) · ∫ f²  =  (window length) · ∫ f² .
```

But the same Cauchy–Schwarz bounds the absolute mass, `L² ≤ (window length) · ∫ f²`.  The two
estimates therefore coincide, and no lower bound for the surplus `L − Bsum` follows from them.  A
continuation must beat one of the two: either show `|f|` is flatter than Cauchy–Schwarz allows
(saturating the bound for `L`), or exhibit genuine cancellation inside the cells (beating it for
`Bsum`).
-/

open Finset

namespace HTGeometry

/-- **The cell estimate of the grid device.**  If each cell integral obeys the per-cell
Cauchy–Schwarz bound `c j ^ 2 ≤ H * Q j`, then the summed cancellation is bounded by the square
root of the window length times the total square mass. -/
theorem sq_sum_abs_le_card_mul_length_mul_total {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (Q : ι → ℝ) {H : ℝ}
    (hcell : ∀ i ∈ s, c i ^ 2 ≤ H * Q i) :
    (∑ i ∈ s, |c i|) ^ 2 ≤ (s.card : ℝ) * H * ∑ i ∈ s, Q i := by
  have h1 : (∑ i ∈ s, |c i|) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, |c i| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : ∑ i ∈ s, |c i| ^ 2 ≤ H * ∑ i ∈ s, Q i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [sq_abs]
    exact hcell i hi
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  calc (∑ i ∈ s, |c i|) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, |c i| ^ 2 := h1
    _ ≤ (s.card : ℝ) * (H * ∑ i ∈ s, Q i) := by exact mul_le_mul_of_nonneg_left h2 hcard
    _ = (s.card : ℝ) * H * ∑ i ∈ s, Q i := by ring

/-- **The collision.**  The absolute mass of a function on the window obeys the same
Cauchy–Schwarz bound as the summed cell cancellation.  So the grid surplus `L - Bsum` cannot be
bounded below using these two estimates alone: both are bounded by `√(window · total square mass)`,
and no gap between them follows. -/
theorem grid_surplus_bounds_coincide {L Bsum W I2 : ℝ}
    (hL : L ^ 2 ≤ W * I2) (hB : Bsum ^ 2 ≤ W * I2) (hL0 : 0 ≤ L) (hB0 : 0 ≤ Bsum) :
    L ≤ Real.sqrt (W * I2) ∧ Bsum ≤ Real.sqrt (W * I2) := by
  constructor
  · rw [show L = Real.sqrt (L ^ 2) from (Real.sqrt_sq hL0).symm]
    exact Real.sqrt_le_sqrt hL
  · rw [show Bsum = Real.sqrt (Bsum ^ 2) from (Real.sqrt_sq hB0).symm]
    exact Real.sqrt_le_sqrt hB

end HTGeometry
