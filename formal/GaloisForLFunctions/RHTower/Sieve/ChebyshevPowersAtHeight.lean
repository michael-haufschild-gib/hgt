import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneTerms

/-!
# The three edge powers against one exponential factor

The five terms of the contour bound involve three powers: `(N+H+1)^{d(T)}` on the right line,
`(N+H+1)^{c(T)}` on the left edge's decay constant, and `(N+H)^{c(T)}` as the left edge's trivial
size.  At the balanced height they are all bounded by the same factor

```text
E = exp( -√(log(N+H+1)) / 160000 ),
```

the right line carrying an extra `T` that the truncation height cancels.  The exponent `1/160000`
is the shifted one: the height is chosen at `Y+1` while the left edge's trivial size is `Y`, and
since `Y + 1 ≤ Y²` the saving `1/80000` merely halves.
-/

namespace RHTower.Sieve

/-- **The shifted left-edge power.** -/
theorem rpow_chebLeftTwo_at_shift {Y : ℝ} (hY : 2 ≤ Y) (hZ : 16 ≤ Real.log (Y + 1)) :
    Y ^ chebLeftTwo (chebHeightOne (Y + 1))
      ≤ Y * Real.exp (-(Real.sqrt (Real.log (Y + 1)) / 160000)) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  rw [rpow_chebLeftTwo hY0]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hY0.le
  have hsq : Y + 1 ≤ Y ^ 2 := by nlinarith
  have hlogY : Real.log (Y + 1) ≤ 2 * Real.log Y := by
    have h1 : Real.log (Y + 1) ≤ Real.log (Y ^ 2) := Real.log_le_log (by linarith) hsq
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hL0 : (0 : ℝ) < Real.log (chebHeightOne (Y + 1)) := by
    have := eight_le_log_chebHeightOne hZ
    linarith
  have hpos : (0 : ℝ) < 1 / 40000 / Real.log (chebHeightOne (Y + 1)) :=
    div_pos (by norm_num) hL0
  have hid := saving_exponent_one hZ
  have hstep : 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log (Y + 1)
      ≤ 2 * (1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log Y) := by
    have hmul := mul_le_mul_of_nonneg_left hlogY hpos.le
    have hring : 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * (2 * Real.log Y)
        = 2 * (1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log Y) := by ring
    linarith [hmul, hring]
  have heq : -(1 / 40000 / Real.log (chebHeightOne (Y + 1))) * Real.log Y
      = -(1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log Y) := by ring
  rw [heq]
  linarith [hid, hstep]

/-- **The unshifted left-edge power against the common factor.** -/
theorem rpow_chebLeftTwo_at_le {Z : ℝ} (hZ0 : 0 < Z) (hZ : 16 ≤ Real.log Z) :
    Z ^ chebLeftTwo (chebHeightOne Z)
      ≤ Z * Real.exp (-(Real.sqrt (Real.log Z) / 160000)) := by
  rw [rpow_chebLeftTwo_at hZ0 hZ]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hZ0.le
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log Z) := Real.sqrt_nonneg _
  linarith

/-- **The right-edge power against the common factor**, with the truncation height to spare. -/
theorem rpow_chebRightTwo_at_le {Z : ℝ} (hZ0 : 0 < Z) (hZ : 16 ≤ Real.log Z) :
    Z ^ chebRightTwo (chebHeightOne Z)
      ≤ Z * Real.exp (-(Real.sqrt (Real.log Z) / 160000)) * chebHeightOne Z := by
  rw [rpow_chebRightTwo_at hZ0 hZ]
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log Z) := Real.sqrt_nonneg _
  have hexp : Real.exp (-(3 / 2) * Real.sqrt (Real.log Z))
      ≤ Real.exp (-(Real.sqrt (Real.log Z) / 160000)) := Real.exp_le_exp.mpr (by linarith)
  have hT0 : (0 : ℝ) ≤ chebHeightOne Z := (chebHeightOne_pos Z).le
  calc Z * (Real.exp (-(3 / 2) * Real.sqrt (Real.log Z)) * chebHeightOne Z)
      ≤ Z * (Real.exp (-(Real.sqrt (Real.log Z) / 160000)) * chebHeightOne Z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hT0) hZ0.le
    _ = Z * Real.exp (-(Real.sqrt (Real.log Z) / 160000)) * chebHeightOne Z := by ring

end RHTower.Sieve
