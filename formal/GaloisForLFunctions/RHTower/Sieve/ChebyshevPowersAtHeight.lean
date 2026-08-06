import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneTerms

/-!
# The three edge powers against one exponential factor

The five terms of the contour bound involve three powers: `(N+H+1)^{d(T)}` on the right line,
`(N+H+1)^{c(T)}` on the left edge's decay constant, and `(N+H)^{c(T)}` as the left edge's trivial
size.  At the balanced height all three are bounded by the same factor

```text
chebFactorOne Z = 3 · exp( -√(log Z) / 80000 ),
```

the right line carrying an extra `T` that the truncation height cancels.

The shift from `Z = Y+1` to `Y` costs only the constant `3`, not half the exponent: `Y + 1 ≤ 2Y`
gives `log Y ≥ log Z - log 2`, and the reciprocal logarithm turns that difference into
`(1/40000)(log 2)/(2√(log Z)) ≤ 1`.  Halving the exponent instead — via the cruder `Z ≤ Y²` — would
leave `1/160000`, which the smoothing's price `exp(√(log N)/120000)` would then swamp.
-/

namespace RHTower.Sieve

/-- The common exponential factor of the three edge powers. -/
noncomputable def chebFactorOne (Z : ℝ) : ℝ :=
  3 * Real.exp (-(Real.sqrt (Real.log Z) / 80000))

theorem chebFactorOne_pos (Z : ℝ) : 0 < chebFactorOne Z := by
  rw [chebFactorOne]
  positivity

/-- **The shifted left-edge power.**  The shift costs the constant `3`, not half the exponent. -/
theorem rpow_chebLeftTwo_at_shift {Y : ℝ} (hY : 1 ≤ Y) (hZ : 16 ≤ Real.log (Y + 1)) :
    Y ^ chebLeftTwo (chebHeightOne (Y + 1)) ≤ Y * chebFactorOne (Y + 1) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  rw [rpow_chebLeftTwo hY0, chebFactorOne]
  refine mul_le_mul_of_nonneg_left ?_ hY0.le
  -- `log Y ≥ log(Y+1) - log 2`
  have hlogY : Real.log (Y + 1) - Real.log 2 ≤ Real.log Y := by
    have h2 : Y + 1 ≤ 2 * Y := by linarith
    have h1 : Real.log (Y + 1) ≤ Real.log (2 * Y) := Real.log_le_log (by linarith) h2
    rw [Real.log_mul (by norm_num) (ne_of_gt hY0)] at h1
    linarith
  have hL8 : (8 : ℝ) ≤ Real.log (chebHeightOne (Y + 1)) := eight_le_log_chebHeightOne hZ
  have hpos : (0 : ℝ) < 1 / 40000 / Real.log (chebHeightOne (Y + 1)) :=
    div_pos (by norm_num) (by linarith)
  have hid := saving_exponent_one hZ
  have hstep : 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * (Real.log (Y + 1) - Real.log 2)
      ≤ 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log Y :=
    mul_le_mul_of_nonneg_left hlogY hpos.le
  have hring : 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * (Real.log (Y + 1) - Real.log 2)
      = 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log (Y + 1)
        - 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log 2 := by ring
  -- the correction is at most one
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hl2' : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsmall : 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log 2 ≤ 1 := by
    have hle : 1 / 40000 / Real.log (chebHeightOne (Y + 1)) ≤ 1 / 40000 / 8 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL8
    nlinarith [hle, hl2, hl2', hpos]
  have hkey : Real.sqrt (Real.log (Y + 1)) / 80000 - 1
      ≤ 1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log Y := by
    linarith [hid, hstep, hring, hsmall]
  -- exponentiate
  have hexp1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  calc Real.exp (-(1 / 40000 / Real.log (chebHeightOne (Y + 1))) * Real.log Y)
      ≤ Real.exp (-(Real.sqrt (Real.log (Y + 1)) / 80000) + 1) := by
        refine Real.exp_le_exp.mpr ?_
        have : -(1 / 40000 / Real.log (chebHeightOne (Y + 1))) * Real.log Y
            = -(1 / 40000 / Real.log (chebHeightOne (Y + 1)) * Real.log Y) := by ring
        rw [this]
        linarith [hkey]
    _ = Real.exp (-(Real.sqrt (Real.log (Y + 1)) / 80000)) * Real.exp 1 := Real.exp_add _ _
    _ ≤ 3 * Real.exp (-(Real.sqrt (Real.log (Y + 1)) / 80000)) := by
        nlinarith [hexp1, Real.exp_pos (-(Real.sqrt (Real.log (Y + 1)) / 80000))]

/-- **The unshifted left-edge power against the common factor.** -/
theorem rpow_chebLeftTwo_at_le {Z : ℝ} (hZ0 : 0 < Z) (hZ : 16 ≤ Real.log Z) :
    Z ^ chebLeftTwo (chebHeightOne Z) ≤ Z * chebFactorOne Z := by
  rw [rpow_chebLeftTwo_at hZ0 hZ, chebFactorOne]
  refine mul_le_mul_of_nonneg_left ?_ hZ0.le
  nlinarith [Real.exp_pos (-(Real.sqrt (Real.log Z) / 80000))]

/-- **The right-edge power against the common factor**, with the truncation height to spare. -/
theorem rpow_chebRightTwo_at_le {Z : ℝ} (hZ0 : 0 < Z) (hZ : 16 ≤ Real.log Z) :
    Z ^ chebRightTwo (chebHeightOne Z) ≤ Z * chebFactorOne Z * chebHeightOne Z := by
  rw [rpow_chebRightTwo_at hZ0 hZ, chebFactorOne]
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log Z) := Real.sqrt_nonneg _
  have hexp : Real.exp (-(3 / 2) * Real.sqrt (Real.log Z))
      ≤ 3 * Real.exp (-(Real.sqrt (Real.log Z) / 80000)) := by
    have h1 : Real.exp (-(3 / 2) * Real.sqrt (Real.log Z))
        ≤ Real.exp (-(Real.sqrt (Real.log Z) / 80000)) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [h1, Real.exp_pos (-(Real.sqrt (Real.log Z) / 80000))]
  have hT0 : (0 : ℝ) ≤ chebHeightOne Z := (chebHeightOne_pos Z).le
  calc Z * (Real.exp (-(3 / 2) * Real.sqrt (Real.log Z)) * chebHeightOne Z)
      ≤ Z * (3 * Real.exp (-(Real.sqrt (Real.log Z) / 80000)) * chebHeightOne Z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hT0) hZ0.le
    _ = Z * (3 * Real.exp (-(Real.sqrt (Real.log Z) / 80000))) * chebHeightOne Z := by ring

end RHTower.Sieve
