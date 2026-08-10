import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlHeight
import GaloisForLFunctions.RHTower.Sieve.ChebyshevRatePowersOne

/-!
# The three edge powers when the depth grows with the height

The trivial sizes the contour bound carries, at the rectangle
`1 - c·log log T/log T ≤ Re s ≤ 1 + 1/log T` and the balanced height
`chebHeightLl c x = exp(√(c·log x·log log x))`.  All three sit under

```text
chebFactorLl c Z = 3·exp(-chebSavingLl c Z) ,     chebSavingLl c Z = ½√(c·log Z·log log Z) ,
```

the left edge because that is what the balance was chosen to give, the right edge and the
truncation because the height is exactly twice the saving in the exponent.
-/

namespace RHTower.Sieve

/-- The common exponential factor of the three edge powers. -/
noncomputable def chebFactorLl (c Z : ℝ) : ℝ := 3 * Real.exp (-(chebSavingLl c Z))

theorem chebFactorLl_pos (c Z : ℝ) : 0 < chebFactorLl c Z := by
  rw [chebFactorLl]; positivity

/-- The left-edge power, split off from the trivial size. -/
theorem rpow_chebLeftLl {c T x : ℝ} (hx : 0 < x) :
    x ^ chebLeftLl c T
      = x * Real.exp (-(c * Real.log (Real.log T) / Real.log T) * Real.log x) := by
  rw [chebLeftLl, Real.rpow_def_of_pos hx,
    show Real.log x * (1 - c * Real.log (Real.log T) / Real.log T)
      = Real.log x + -(c * Real.log (Real.log T) / Real.log T) * Real.log x by ring,
    Real.exp_add, Real.exp_log hx]

/-- The rectangle's width coefficient at the balanced height is at most `1/8`. -/
theorem left_width_le_eighth {c Z : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 2)
    (hQ : 256 ≤ chebQuadLl c Z) :
    c * Real.log (Real.log (chebHeightLl c Z)) / Real.log (chebHeightLl c Z) ≤ 1 / 8 := by
  have hs8 : (8 : ℝ) ≤ chebSavingLl c Z := eight_le_chebSavingLl hQ
  have hLg : Real.log (chebHeightLl c Z) = 2 * chebSavingLl c Z := log_chebHeightLl c Z
  have hLg0 : (0 : ℝ) < Real.log (chebHeightLl c Z) := by rw [hLg]; linarith
  have h8 := eight_mul_chebDepthLl_le hc0 hc hQ
  rw [chebDepthLl] at h8
  rw [div_le_div_iff₀ hLg0 (by norm_num)]
  linarith

/-- The rectangle's width coefficient at the balanced height is nonnegative. -/
theorem left_width_nonneg {c Z : ℝ} (hc0 : 0 < c) (hQ : 256 ≤ chebQuadLl c Z) :
    0 ≤ c * Real.log (Real.log (chebHeightLl c Z)) / Real.log (chebHeightLl c Z) := by
  have h16 := sixteen_le_log_chebHeightLl hQ
  have hLL : (0 : ℝ) ≤ Real.log (Real.log (chebHeightLl c Z)) :=
    Real.log_nonneg (by linarith)
  have hLg0 : (0 : ℝ) < Real.log (chebHeightLl c Z) := by linarith
  positivity

/-- **The unshifted left-edge power against the common factor.** -/
theorem rpow_chebLeftLl_at_le {c Z : ℝ} (hc0 : 0 < c) (hZ0 : 0 < Z) (hlogZ : 0 < Real.log Z)
    (hQ : 256 ≤ chebQuadLl c Z) (hcx : Real.log Z ≤ chebQuadLl c Z) :
    Z ^ chebLeftLl c (chebHeightLl c Z) ≤ Z * chebFactorLl c Z := by
  rw [rpow_chebLeftLl hZ0, chebFactorLl]
  refine mul_le_mul_of_nonneg_left ?_ hZ0.le
  have hsave := chebSavingLl_le_left_saving hc0 hlogZ hQ hcx
  have hexp : Real.exp
      (-(c * Real.log (Real.log (chebHeightLl c Z)) / Real.log (chebHeightLl c Z)) * Real.log Z)
      ≤ Real.exp (-(chebSavingLl c Z)) := by
    refine Real.exp_le_exp.mpr ?_
    have heq : -(c * Real.log (Real.log (chebHeightLl c Z)) / Real.log (chebHeightLl c Z))
          * Real.log Z
        = -(c * Real.log (Real.log (chebHeightLl c Z)) / Real.log (chebHeightLl c Z)
            * Real.log Z) := by ring
    rw [heq]
    linarith
  nlinarith [hexp, Real.exp_pos (-(chebSavingLl c Z))]

/-- **The shifted left-edge power.**  The shift from `Y + 1` to `Y` costs the constant `3`. -/
theorem rpow_chebLeftLl_at_shift {c Y : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hY : 1 ≤ Y)
    (hlogZ : 0 < Real.log (Y + 1)) (hQ : 256 ≤ chebQuadLl c (Y + 1))
    (hcx : Real.log (Y + 1) ≤ chebQuadLl c (Y + 1)) :
    Y ^ chebLeftLl c (chebHeightLl c (Y + 1)) ≤ Y * chebFactorLl c (Y + 1) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  rw [rpow_chebLeftLl hY0, chebFactorLl]
  refine mul_le_mul_of_nonneg_left ?_ hY0.le
  set w : ℝ := c * Real.log (Real.log (chebHeightLl c (Y + 1)))
      / Real.log (chebHeightLl c (Y + 1)) with hwdef
  have hw0 : (0 : ℝ) ≤ w := left_width_nonneg hc0 hQ
  have hw8 : w ≤ 1 / 8 := left_width_le_eighth hc0 hc hQ
  have hsave : chebSavingLl c (Y + 1) ≤ w * Real.log (Y + 1) :=
    chebSavingLl_le_left_saving hc0 hlogZ hQ hcx
  -- `log Y ≥ log(Y+1) - log 2`
  have hlogY : Real.log (Y + 1) - Real.log 2 ≤ Real.log Y := by
    have h2 : Y + 1 ≤ 2 * Y := by linarith
    have h1 : Real.log (Y + 1) ≤ Real.log (2 * Y) := Real.log_le_log (by linarith) h2
    rw [Real.log_mul (by norm_num) (ne_of_gt hY0)] at h1
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hstep : w * (Real.log (Y + 1) - Real.log 2) ≤ w * Real.log Y :=
    mul_le_mul_of_nonneg_left hlogY hw0
  have hsmall : w * Real.log 2 ≤ 1 := by nlinarith [hw8, hlog2, hlog2nn]
  have hkey : chebSavingLl c (Y + 1) - 1 ≤ w * Real.log Y := by nlinarith [hstep, hsave, hsmall]
  have hexp1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  calc Real.exp (-w * Real.log Y)
      ≤ Real.exp (-(chebSavingLl c (Y + 1)) + 1) := by
        refine Real.exp_le_exp.mpr ?_
        have hneg : -w * Real.log Y = -(w * Real.log Y) := by ring
        rw [hneg]
        linarith [hkey]
    _ = Real.exp (-(chebSavingLl c (Y + 1))) * Real.exp 1 := Real.exp_add _ _
    _ ≤ 3 * Real.exp (-(chebSavingLl c (Y + 1))) := by
        nlinarith [hexp1, Real.exp_pos (-(chebSavingLl c (Y + 1)))]

/-- **The right-edge power against the common factor**, with the height to spare. -/
theorem rpow_chebRightTwo_at_ll_le {c Z : ℝ} (hZ0 : 0 < Z) (hQ : 256 ≤ chebQuadLl c Z)
    (h2 : 2 * Real.log Z ≤ chebQuadLl c Z) :
    Z ^ chebRightTwo (chebHeightLl c Z) ≤ Z * chebFactorLl c Z * chebHeightLl c Z := by
  have hright := right_cost_le_chebSavingLl hQ h2
  rw [log_chebHeightLl] at hright
  have hHeq : chebHeightLl c Z = Real.exp (2 * chebSavingLl c Z) := by
    rw [chebHeightLl, chebSavingLl]; congr 1; ring
  rw [rpow_chebRightTwo hZ0, chebFactorLl, log_chebHeightLl, hHeq]
  have hexp : Real.exp (1 / (2 * chebSavingLl c Z) * Real.log Z)
      ≤ 3 * Real.exp (-(chebSavingLl c Z)) * Real.exp (2 * chebSavingLl c Z) := by
    have heq : (3 : ℝ) * Real.exp (-(chebSavingLl c Z)) * Real.exp (2 * chebSavingLl c Z)
        = 3 * Real.exp (-(chebSavingLl c Z) + 2 * chebSavingLl c Z) := by
      rw [Real.exp_add]; ring
    rw [heq]
    have hle : Real.exp (1 / (2 * chebSavingLl c Z) * Real.log Z)
        ≤ Real.exp (-(chebSavingLl c Z) + 2 * chebSavingLl c Z) :=
      Real.exp_le_exp.mpr (by linarith)
    nlinarith [hle, Real.exp_pos (-(chebSavingLl c Z) + 2 * chebSavingLl c Z)]
  calc Z * Real.exp (1 / (2 * chebSavingLl c Z) * Real.log Z)
      ≤ Z * (3 * Real.exp (-(chebSavingLl c Z)) * Real.exp (2 * chebSavingLl c Z)) :=
        mul_le_mul_of_nonneg_left hexp hZ0.le
    _ = Z * (3 * Real.exp (-(chebSavingLl c Z))) * Real.exp (2 * chebSavingLl c Z) := by ring

/-- The reciprocal of the height is under the common factor. -/
theorem one_div_chebHeightLl_le_factor (c Z : ℝ) :
    1 / chebHeightLl c Z ≤ chebFactorLl c Z := by
  have hsL : Real.sqrt (chebQuadLl c Z) = 2 * chebSavingLl c Z := by
    rw [chebSavingLl]; ring
  rw [chebHeightLl, chebFactorLl, one_div, ← Real.exp_neg, hsL]
  have hs : (0 : ℝ) ≤ chebSavingLl c Z := chebSavingLl_nonneg c Z
  have h1 : Real.exp (-(2 * chebSavingLl c Z)) ≤ Real.exp (-(chebSavingLl c Z)) :=
    Real.exp_le_exp.mpr (by linarith)
  nlinarith [h1, Real.exp_pos (-(chebSavingLl c Z))]

end RHTower.Sieve
