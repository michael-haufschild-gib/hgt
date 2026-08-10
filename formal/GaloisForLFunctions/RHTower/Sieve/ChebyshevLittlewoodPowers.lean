import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodHeight
import GaloisForLFunctions.RHTower.Sieve.ChebyshevRatePowersOne

/-!
# The three edge powers at depth `A`

The three trivial sizes the contour bound carries, at the rectangle
`1 - A/log T ≤ Re s ≤ 1 + 1/log T` and the balanced height `chebHeightLw A x = exp(2√(A log x))`.
All three are measured against the common factor

```text
chebFactorLw A Z = 3·exp(-√(A log Z)/2) ,
```

whose exponent is the saving of `saving_exponent_lw`.  Depth `A ≥ 1` is assumed throughout: it is
what makes the right edge fit under the same factor (`1/(2A) ≤ 3/2`), and it is the regime the
Littlewood region exists to reach.
-/

namespace RHTower.Sieve

/-- The common exponential factor of the three edge powers at depth `A`. -/
noncomputable def chebFactorLw (A Z : ℝ) : ℝ :=
  3 * Real.exp (-(Real.sqrt (A * Real.log Z) / 2))

theorem chebFactorLw_pos (A Z : ℝ) : 0 < chebFactorLw A Z := by
  rw [chebFactorLw]
  positivity

/-- The left-edge power, split off from the trivial size. -/
theorem rpow_chebLeftLw {A T x : ℝ} (hx : 0 < x) :
    x ^ chebLeftLw A T = x * Real.exp (-(A / Real.log T) * Real.log x) := by
  rw [chebLeftLw, Real.rpow_def_of_pos hx,
    show Real.log x * (1 - A / Real.log T)
      = Real.log x + -(A / Real.log T) * Real.log x by ring,
    Real.exp_add, Real.exp_log hx]

/-- **The left-edge power at the balanced height.** -/
theorem rpow_chebLeftLw_at {A x : ℝ} (hA : 0 < A) (hx0 : 0 < x) (hx : 0 < Real.log x) :
    x ^ chebLeftLw A (chebHeightLw A x)
      = x * Real.exp (-(Real.sqrt (A * Real.log x) / 2)) := by
  rw [rpow_chebLeftLw hx0]
  congr 1
  congr 1
  have h := saving_exponent_lw hA hx
  linarith [h]

/-- **The unshifted left-edge power against the common factor.** -/
theorem rpow_chebLeftLw_at_le {A Z : ℝ} (hA : 0 < A) (hZ0 : 0 < Z) (hZ : 0 < Real.log Z) :
    Z ^ chebLeftLw A (chebHeightLw A Z) ≤ Z * chebFactorLw A Z := by
  rw [rpow_chebLeftLw_at hA hZ0 hZ, chebFactorLw]
  refine mul_le_mul_of_nonneg_left ?_ hZ0.le
  nlinarith [Real.exp_pos (-(Real.sqrt (A * Real.log Z) / 2))]

/-- **The shifted left-edge power.**  The shift from `Y + 1` to `Y` costs the constant `3`. -/
theorem rpow_chebLeftLw_at_shift {A Y : ℝ} (hA : 0 < A) (hY : 1 ≤ Y)
    (hAY : A ≤ Real.log (Y + 1)) :
    Y ^ chebLeftLw A (chebHeightLw A (Y + 1)) ≤ Y * chebFactorLw A (Y + 1) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY1 : (0 : ℝ) < Real.log (Y + 1) := by nlinarith
  rw [rpow_chebLeftLw hY0, chebFactorLw]
  refine mul_le_mul_of_nonneg_left ?_ hY0.le
  set u : ℝ := Real.sqrt (A * Real.log (Y + 1)) with hudef
  have hu0 : (0 : ℝ) < u := Real.sqrt_pos.mpr (by positivity)
  have husq : u * u = A * Real.log (Y + 1) := Real.mul_self_sqrt (by positivity)
  have hLT : Real.log (chebHeightLw A (Y + 1)) = 2 * u := by
    rw [log_chebHeightLw, ← hudef]
  -- `log Y ≥ log(Y+1) - log 2`
  have hlogY : Real.log (Y + 1) - Real.log 2 ≤ Real.log Y := by
    have h2 : Y + 1 ≤ 2 * Y := by linarith
    have h1 : Real.log (Y + 1) ≤ Real.log (2 * Y) := Real.log_le_log (by linarith) h2
    rw [Real.log_mul (by norm_num) (ne_of_gt hY0)] at h1
    linarith
  have hcoef : A / Real.log (chebHeightLw A (Y + 1)) = A / (2 * u) := by rw [hLT]
  have hcoefpos : (0 : ℝ) < A / (2 * u) := by positivity
  -- the coefficient is at most `1/2`
  have hcoefsmall : A / (2 * u) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [husq, hu0, hA, hAY]
  -- the main exponent
  have hmain : A / (2 * u) * Real.log (Y + 1) = u / 2 := by
    field_simp
    nlinarith [husq, hu0]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hstep : A / (2 * u) * (Real.log (Y + 1) - Real.log 2) ≤ A / (2 * u) * Real.log Y :=
    mul_le_mul_of_nonneg_left hlogY hcoefpos.le
  have hsmall : A / (2 * u) * Real.log 2 ≤ 1 := by nlinarith [hcoefsmall, hlog2, hlog2nn]
  have hkey : u / 2 - 1 ≤ A / (2 * u) * Real.log Y := by nlinarith [hstep, hmain, hsmall]
  have hexp1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  rw [hcoef]
  calc Real.exp (-(A / (2 * u)) * Real.log Y)
      ≤ Real.exp (-(u / 2) + 1) := by
        refine Real.exp_le_exp.mpr ?_
        have hneg : -(A / (2 * u)) * Real.log Y = -(A / (2 * u) * Real.log Y) := by ring
        rw [hneg]
        linarith [hkey]
    _ = Real.exp (-(u / 2)) * Real.exp 1 := Real.exp_add _ _
    _ ≤ 3 * Real.exp (-(u / 2)) := by
        nlinarith [hexp1, Real.exp_pos (-(u / 2))]

/-- **The right-edge power against the common factor**, with the height to spare. -/
theorem rpow_chebRightTwo_at_lw_le {A Z : ℝ} (hA : 1 ≤ A) (hZ0 : 0 < Z) (hZ : 0 < Real.log Z) :
    Z ^ chebRightTwo (chebHeightLw A Z) ≤ Z * chebFactorLw A Z * chebHeightLw A Z := by
  have hA0 : (0 : ℝ) < A := by linarith
  rw [rpow_chebRightTwo hZ0]
  set u : ℝ := Real.sqrt (A * Real.log Z) with hudef
  have hu0 : (0 : ℝ) ≤ u := Real.sqrt_nonneg _
  have hright := right_exponent_lw hA0 hZ
  rw [← hudef] at hright
  rw [hright, chebFactorLw, chebHeightLw, ← hudef]
  have hexp : Real.exp (u / (2 * A)) ≤ 3 * Real.exp (-(u / 2)) * Real.exp (2 * u) := by
    have heq : (3 : ℝ) * Real.exp (-(u / 2)) * Real.exp (2 * u)
        = 3 * Real.exp (-(u / 2) + 2 * u) := by
      rw [Real.exp_add]; ring
    rw [heq]
    have hle : Real.exp (u / (2 * A)) ≤ Real.exp (-(u / 2) + 2 * u) := by
      refine Real.exp_le_exp.mpr ?_
      have hbound : u / (2 * A) ≤ u / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hu0, hA]
      linarith
    nlinarith [hle, Real.exp_pos (-(u / 2) + 2 * u)]
  calc Z * Real.exp (u / (2 * A))
      ≤ Z * (3 * Real.exp (-(u / 2)) * Real.exp (2 * u)) :=
        mul_le_mul_of_nonneg_left hexp hZ0.le
    _ = Z * (3 * Real.exp (-(u / 2))) * Real.exp (2 * u) := by ring

/-- The reciprocal of the height is under the common factor. -/
theorem one_div_chebHeightLw_le_factor (A Z : ℝ) :
    1 / chebHeightLw A Z ≤ chebFactorLw A Z := by
  rw [chebHeightLw, chebFactorLw, one_div, ← Real.exp_neg]
  have hs : (0 : ℝ) ≤ Real.sqrt (A * Real.log Z) := Real.sqrt_nonneg _
  have h1 : Real.exp (-(2 * Real.sqrt (A * Real.log Z)))
      ≤ Real.exp (-(Real.sqrt (A * Real.log Z) / 2)) := Real.exp_le_exp.mpr (by linarith)
  nlinarith [h1, Real.exp_pos (-(Real.sqrt (A * Real.log Z) / 2))]

end RHTower.Sieve
