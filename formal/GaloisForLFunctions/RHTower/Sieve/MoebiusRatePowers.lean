import GaloisForLFunctions.RHTower.Sieve.MoebiusContourParamTwo

/-!
# The two edge powers at the balanced parameter

At `K = contourParamTwo Z` the two trivial sizes of the contour bound separate into the cutoff
itself times an explicit factor:

```text
Z^{d(K)} ≤ Z · exp(-(7/4)(log Z)^{1/3}) · K,      Z^{c(K)} ≤ Z · exp(-(log Z)^{1/3}/9).
```

The first is what lets the truncation height `≍ K` absorb the growth of the right line; the second
is the left edge's saving.  A third form is needed because the parameter is chosen at `Y+1` while
the left edge's trivial size is `Y`: there the saving halves, to `exp(-(log(Y+1))^{1/3}/18)`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The right-edge power, split off from the trivial size. -/
theorem rpow_rightAbscissaTwo {K : ℕ} {x : ℝ} (hx : 0 < x) :
    x ^ rightAbscissaTwo K = x * Real.exp (1 / (Real.log K) ^ 2 * Real.log x) := by
  rw [rightAbscissaTwo, Real.rpow_def_of_pos hx,
    show Real.log x * (1 + 1 / (Real.log K) ^ 2)
      = Real.log x + 1 / (Real.log K) ^ 2 * Real.log x by ring,
    Real.exp_add, Real.exp_log hx]

/-- The parameter exceeds seven. -/
theorem seven_le_contourParamTwo {x : ℝ} (hx : 1 ≤ Real.log x) :
    (7 : ℝ) ≤ (contourParamTwo x : ℝ) := by
  have ht1 : (1 : ℝ) ≤ (Real.log x) ^ ((1 : ℝ) / 3) := Real.one_le_rpow hx (by norm_num)
  have h2 : Real.exp 2 ≤ Real.exp (2 * (Real.log x) ^ ((1 : ℝ) / 3)) :=
    Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have he1 := Real.exp_one_gt_d9
  have h7 : (7 : ℝ) ≤ Real.exp 2 := by nlinarith [he, he1]
  linarith [exp_le_contourParamTwo x, h2, h7]

/-- **The right-edge power at the balanced parameter.** -/
theorem rpow_rightAbscissaTwo_le {Z : ℝ} (hZ : 0 < Z) (hlogZ : 1 ≤ Real.log Z) :
    Z ^ rightAbscissaTwo (contourParamTwo Z)
      ≤ Z * Real.exp (-(7 / 4) * (Real.log Z) ^ ((1 : ℝ) / 3)) * (contourParamTwo Z : ℝ) := by
  rw [rpow_rightAbscissaTwo hZ]
  calc Z * Real.exp (1 / (Real.log (contourParamTwo Z)) ^ 2 * Real.log Z)
      ≤ Z * (Real.exp (-(7 / 4) * (Real.log Z) ^ ((1 : ℝ) / 3)) * (contourParamTwo Z : ℝ)) :=
        mul_le_mul_of_nonneg_left (exp_saving_right_two hlogZ) hZ.le
    _ = Z * Real.exp (-(7 / 4) * (Real.log Z) ^ ((1 : ℝ) / 3)) * (contourParamTwo Z : ℝ) := by
        ring

/-- **The left-edge power at the balanced parameter.** -/
theorem rpow_leftAbscissaTwo_le {Z : ℝ} (hZ : 0 < Z) (hlogZ : 1 ≤ Real.log Z) :
    Z ^ leftAbscissaTwo (contourParamTwo Z)
      ≤ Z * Real.exp (-((Real.log Z) ^ ((1 : ℝ) / 3) / 9)) := by
  rw [rpow_leftAbscissaTwo hZ]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hZ.le
  have h := le_saving_exponent_two hlogZ
  have heq : -(1 / (Real.log (contourParamTwo Z)) ^ 2) * Real.log Z
      = -(1 / (Real.log (contourParamTwo Z)) ^ 2 * Real.log Z) := by ring
  rw [heq]
  linarith [h]

/-- **The shifted left-edge power.**  The parameter is chosen at `Y+1` while the left edge's
trivial size is `Y`; since `Y + 1 ≤ Y²`, the saving is halved. -/
theorem rpow_leftAbscissaTwo_le_shift {Y : ℝ} (hY : 2 ≤ Y) (hlogZ : 1 ≤ Real.log (Y + 1)) :
    Y ^ leftAbscissaTwo (contourParamTwo (Y + 1))
      ≤ Y * Real.exp (-((Real.log (Y + 1)) ^ ((1 : ℝ) / 3) / 18)) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  rw [rpow_leftAbscissaTwo hY0]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hY0.le
  have hsq : Y + 1 ≤ Y ^ 2 := by nlinarith
  have hlogY : Real.log (Y + 1) ≤ 2 * Real.log Y := by
    have h1 : Real.log (Y + 1) ≤ Real.log (Y ^ 2) := Real.log_le_log (by linarith) hsq
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have h := le_saving_exponent_two hlogZ
  set Λ : ℝ := Real.log (contourParamTwo (Y + 1)) with hΛdef
  have ht1 : (1 : ℝ) ≤ (Real.log (Y + 1)) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow hlogZ (by norm_num)
  have hΛ0 : (0 : ℝ) < Λ := by
    have hlow := le_log_contourParamTwo (Y + 1)
    rw [hΛdef]
    linarith
  have hΛpos : (0 : ℝ) < 1 / Λ ^ 2 := by positivity
  have hstep : 1 / Λ ^ 2 * Real.log (Y + 1) ≤ 2 * (1 / Λ ^ 2 * Real.log Y) := by
    have hmul := mul_le_mul_of_nonneg_left hlogY hΛpos.le
    have hring : 1 / Λ ^ 2 * (2 * Real.log Y) = 2 * (1 / Λ ^ 2 * Real.log Y) := by ring
    linarith [hmul, hring]
  have heq : -(1 / Λ ^ 2) * Real.log Y = -(1 / Λ ^ 2 * Real.log Y) := by ring
  rw [heq]
  linarith [h, hstep]

end RHTower.Sieve
