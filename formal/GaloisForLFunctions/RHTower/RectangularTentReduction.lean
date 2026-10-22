import GaloisForLFunctions.RHTower.CCM.CCMRectangularAutocorrelation

/-!
# On the arithmetic range the rectangular autocorrelation has only two tents

The two-edge autocorrelation expands into four tents,

```text
R(L,a,h) = 2·max(0, L−|h|) + max(0, L−|h−(2a−L)|) + max(0, L−|h+(2a−L)|) ,
```

but the prime wall evaluates it only at `h = log k` with `k ≥ 1`, so `h ≥ 0`.  Under the window
hypothesis `L ≤ a` the third tent is centred at `h = −(2a−L) ≤ −L`, and its support
`(−(2a−L)−L, −(2a−L)+L)` lies entirely in `h < 0` — except in the degenerate case `a = L`, where it
touches `h = 0` only at the endpoint and still vanishes.  Hence it contributes nothing to any
arithmetic sample.

So on the arithmetic range the autocorrelation is exactly

```text
R(L,a,log k) = 2·max(0, L − log k)  +  max(0, L − |log k − (2a−L)|) ,
```

a **fixed** tent at the origin, supported on `k < e^{L}` and independent of the aperture, plus a
single **moving** tent centred at `log k = 2a−L`, supported on `k ∈ (e^{2a−2L}, e^{2a})`.  With
`a = ½log n` the moving tent occupies the multiplicative window `(n·e^{−2L}, n)`.

This is the structure the criterion actually compares against its archimedean budget: a constant and
a window of fixed multiplicative width riding at the top of the range.
-/

open Real

namespace RHTower

/-- **The reflected tent vanishes at nonnegative lag.**  For `0 < L ≤ a` and `h ≥ 0` the tent
centred at `−(2a−L)` contributes nothing. -/
theorem reflected_tent_eq_zero {L a h : ℝ} (hL : 0 < L) (ha : L ≤ a) (hh : 0 ≤ h) :
    max 0 (L - |h + (2 * a - L)|) = 0 := by
  have hcen : 0 < 2 * a - L := by linarith
  have hpos : 0 ≤ h + (2 * a - L) := by linarith
  rw [abs_of_nonneg hpos, max_eq_left]
  linarith

/-- **Two-tent form on nonnegative lag.**  At every nonnegative lag the autocorrelation is the fixed
tent plus the single moving tent. -/
theorem rectangularTwoEdgeAutocorrelation_eq_two_tents {L a h : ℝ}
    (hL : 0 < L) (ha : L ≤ a) (hh : 0 ≤ h) :
    rectangularTwoEdgeAutocorrelation L a h =
      2 * max 0 (L - |h|) + max 0 (L - |h - (2 * a - L)|) := by
  rw [rectangularTwoEdgeAutocorrelation_eq_four_tents, reflected_tent_eq_zero hL ha hh, add_zero]

/-- **Two-tent form at an arithmetic sample.**  Specialized to `h = log k` with `k ≥ 1`, where the
absolute value on the fixed tent also disappears. -/
theorem rectangularTwoEdgeAutocorrelation_log_eq_two_tents {L a : ℝ} {k : ℕ}
    (hL : 0 < L) (ha : L ≤ a) (hk : 1 ≤ k) :
    rectangularTwoEdgeAutocorrelation L a (Real.log k) =
      2 * max 0 (L - Real.log k) + max 0 (L - |Real.log k - (2 * a - L)|) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  rw [rectangularTwoEdgeAutocorrelation_eq_two_tents hL ha hlog, abs_of_nonneg hlog]

/-- **The fixed tent is supported below `e^{L}`.**  Beyond that threshold only the moving tent can
contribute, so the aperture-independent part of the prime wall is a finite sum whose range never
changes. -/
theorem fixed_tent_eq_zero_of_le_log {L : ℝ} {k : ℕ} (hk : L ≤ Real.log k) :
    max 0 (L - Real.log k) = 0 := by
  rw [max_eq_left]
  linarith

/-- **The moving tent is supported in the multiplicative window `(e^{2a−2L}, e^{2a})`.**  Outside
that window it contributes nothing, so the aperture-dependent part of the prime wall is a sum over a
window of fixed multiplicative width riding at the top of the range. -/
theorem moving_tent_eq_zero_of_outside {L a : ℝ} {k : ℕ} (hL : 0 ≤ L)
    (h : Real.log k ≤ 2 * a - 2 * L ∨ 2 * a ≤ Real.log k) :
    max 0 (L - |Real.log k - (2 * a - L)|) = 0 := by
  rw [max_eq_left]
  rcases h with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- **The two tents never overlap once the aperture clears three halves of the width.**  For
`3L ≤ 2a` the fixed tent's support `log k < L` and the moving tent's support `log k > 2a − 2L` are
disjoint, so past that aperture the prime wall is a disjoint sum of a constant and a moving window.
The threshold is sharp: at `3L = 2a` the two supports meet at the single point `log k = L`. -/
theorem tent_supports_disjoint {L a : ℝ} (hL : 0 < L) (ha : 3 * L ≤ 2 * a) {k : ℕ}
    (hfix : Real.log k < L) :
    max 0 (L - |Real.log k - (2 * a - L)|) = 0 := by
  refine moving_tent_eq_zero_of_outside hL.le (Or.inl ?_)
  linarith

end RHTower
