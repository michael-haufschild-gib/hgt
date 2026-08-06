import GaloisForLFunctions.RHTower.Sieve.ChebyshevHeightOne

/-!
# The two edge powers at the balanced height

At `T = chebHeightOne x` the two trivial sizes of the Chebyshev contour bound separate into the
cutoff itself times an explicit factor, and both separations are *exact*:

```text
x^{c(T)} = x · exp(-√(log x)/80000),      x^{d(T)} = x · exp(-(3/2)√(log x)) · T.
```

The first is the left edge's saving; the second is what the truncation height `T` absorbs.
-/

namespace RHTower.Sieve

/-- The right-edge power, split off from the trivial size. -/
theorem rpow_chebRightTwo {T x : ℝ} (hx : 0 < x) :
    x ^ chebRightTwo T = x * Real.exp (1 / Real.log T * Real.log x) := by
  rw [chebRightTwo, Real.rpow_def_of_pos hx,
    show Real.log x * (1 + 1 / Real.log T) = Real.log x + 1 / Real.log T * Real.log x by ring,
    Real.exp_add, Real.exp_log hx]

/-- The left-edge power, split off from the trivial size. -/
theorem rpow_chebLeftTwo {T x : ℝ} (hx : 0 < x) :
    x ^ chebLeftTwo T = x * Real.exp (-(1 / 40000 / Real.log T) * Real.log x) := by
  rw [chebLeftTwo, Real.rpow_def_of_pos hx,
    show Real.log x * (1 - 1 / 40000 / Real.log T)
      = Real.log x + -(1 / 40000 / Real.log T) * Real.log x by ring,
    Real.exp_add, Real.exp_log hx]

/-- **The left-edge power at the balanced height.** -/
theorem rpow_chebLeftTwo_at {x : ℝ} (hx0 : 0 < x) (hx : 16 ≤ Real.log x) :
    x ^ chebLeftTwo (chebHeightOne x) = x * Real.exp (-(Real.sqrt (Real.log x) / 80000)) := by
  rw [rpow_chebLeftTwo hx0]
  congr 1
  congr 1
  have h := saving_exponent_one hx
  linarith [h]

/-- **The right-edge power at the balanced height.** -/
theorem rpow_chebRightTwo_at {x : ℝ} (hx0 : 0 < x) (hx : 16 ≤ Real.log x) :
    x ^ chebRightTwo (chebHeightOne x)
      = x * (Real.exp (-(3 / 2) * Real.sqrt (Real.log x)) * chebHeightOne x) := by
  rw [rpow_chebRightTwo hx0, exp_right_le_chebHeightOne hx]

end RHTower.Sieve
