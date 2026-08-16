import GaloisForLFunctions.RHTower.BandEndpointPhaseSharp

/-!
# The logarithmic derivative of the band phase, minus its singular part

The band phase has `Xi'/Xi ~ -1/(2(1-y))` at the endpoint, the same rate as `-y/(1-y²)`.  Their
difference

```text
L_s(y) = Xi'/Xi + y/(1-y²) = -sqrt((y²-s)/(1-y²)) / Xi_s(y) + y/(1-y²)
```

is bounded, uniformly in `s ≤ 1/2` and up to the endpoint.  This is what makes the comparison defect
of the band a simple pole rather than a double one: writing `Xi'/Xi = -y/(1-y²) + L` turns the
transcendental square `(Xi'/Xi)²/4` into an explicit rational double pole plus terms carrying at
least one factor of `L`.

Both bounds come from the endpoint squeeze of `Xi`.  The upper bound uses the upper squeeze together
with `sqrt(1-z) ≥ 1-z`; the lower bound uses the lower squeeze and then only `1+y ≤ 2`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The logarithmic derivative of the band phase with its explicit singular part removed. -/
def bandPhaseLogDefect (s y : ℝ) : ℝ :=
  -(prolateWKBProfile s y) / bandEndpointPhase s y + y / (1 - y ^ 2)

section

variable {s y : ℝ}

/-- **The defect from above.** -/
theorem bandPhaseLogDefect_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hy0 : 0 < y) (hy1 : y < 1) (hsy : s < y ^ 2) :
    bandPhaseLogDefect s y ≤ 2 := by
  have hy2 : y ^ 2 < 1 := by nlinarith
  have h1y2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  set p := Real.sqrt (1 - y) with hpdef
  set q := Real.sqrt (1 + y) with hqdef
  set w := Real.sqrt (y ^ 2 - s) with hwdef
  set v := Real.sqrt (1 - s) with hvdef
  have hp : 0 < p := Real.sqrt_pos.2 (by linarith)
  have hq : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hw : 0 < w := Real.sqrt_pos.2 (by linarith)
  have hv : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hp2 : p ^ 2 = 1 - y := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = 1 + y := Real.sq_sqrt (by linarith)
  have hw2 : w ^ 2 = y ^ 2 - s := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
  have hvw : w ≤ v := by nlinarith
  have hXi : 0 < bandEndpointPhase s y := bandEndpointPhase_pos hy1 hsy hy0
  have hProf : prolateWKBProfile s y = w / (p * q) := by
    rw [prolateWKBProfile_eq_div hsy.le, hwdef, hpdef, hqdef, ← Real.sqrt_mul (by linarith)]
    ring_nf
  -- the upper squeeze in a division-free form
  have hub2 : bandEndpointPhase s y ≤ 2 * v * p / q := by
    have h := bandEndpointPhase_le_sharp (s := s) hy0.le hy1.le
    calc bandEndpointPhase s y ≤ Real.sqrt (1 - s) *
          (2 * Real.sqrt (1 - y) / Real.sqrt (1 + y)) := h
      _ = 2 * v * p / q := by rw [hvdef, hpdef, hqdef]; ring
  have hub' : bandEndpointPhase s y * q ≤ 2 * v * p := (le_div_iff₀ hq).mp hub2
  -- the model quotient from below
  have hquot : w / (2 * v * p ^ 2) ≤ prolateWKBProfile s y / bandEndpointPhase s y := by
    rw [hProf, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hub' hp.le]
  -- the rational inequality
  have hpolyv : 2 * (1 - s) * y - (y ^ 2 - s) * (1 + y) ≤ 4 * (1 - s) * (1 - y ^ 2) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - y)
      (by nlinarith : (0:ℝ) ≤ 4 + 2 * y - y ^ 2 - s * (4 * y + 5))]
  have hA : (y ^ 2 - s) * (1 + y) ≤ w * (1 + y) * v := by
    nlinarith [mul_le_mul_of_nonneg_right hvw (by positivity : (0:ℝ) ≤ w * (1 + y))]
  have hmulv : (2 * v * y - w * (1 + y)) * v ≤ (4 * v * (1 - y ^ 2)) * v := by
    nlinarith [hA, hv2, hpolyv]
  have hfinal : 2 * v * y - w * (1 + y) ≤ 4 * v * (1 - y ^ 2) :=
    le_of_mul_le_mul_right hmulv hv
  have key : y * (2 * v * (1 - y)) - (1 - y ^ 2) * w
      ≤ 2 * ((1 - y ^ 2) * (2 * v * (1 - y))) := by
    nlinarith [hfinal, hy1]
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have hden : (0 : ℝ) < 2 * v * (1 - y) := mul_pos (by linarith) h1y
  have hsplit : y / (1 - y ^ 2) - w / (2 * v * (1 - y))
      = (y * (2 * v * (1 - y)) - (1 - y ^ 2) * w) / ((1 - y ^ 2) * (2 * v * (1 - y))) :=
    div_sub_div _ _ (ne_of_gt h1y2) (ne_of_gt hden)
  have hstep2 : y / (1 - y ^ 2) - w / (2 * v * p ^ 2) ≤ 2 := by
    rw [hp2, hsplit, div_le_iff₀ (by positivity)]
    linarith [key]
  rw [bandPhaseLogDefect, neg_div]
  linarith [hquot, hstep2]

/-- **The defect from below.** -/
theorem le_bandPhaseLogDefect (hy0 : 0 < y) (hy1 : y < 1) (hsy : s < y ^ 2) :
    -2 ≤ bandPhaseLogDefect s y := by
  have hy2 : y ^ 2 < 1 := by nlinarith
  have h1y2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  set p := Real.sqrt (1 - y) with hpdef
  set q := Real.sqrt (1 + y) with hqdef
  set w := Real.sqrt (y ^ 2 - s) with hwdef
  set r := Real.sqrt 2 with hrdef
  have hp : 0 < p := Real.sqrt_pos.2 (by linarith)
  have hq : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hw : 0 < w := Real.sqrt_pos.2 (by linarith)
  have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hp2 : p ^ 2 = 1 - y := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = 1 + y := Real.sq_sqrt (by linarith)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hqr : q ≤ r := by
    rw [hqdef, hrdef]
    exact Real.sqrt_le_sqrt (by linarith)
  have hXi : 0 < bandEndpointPhase s y := bandEndpointPhase_pos hy1 hsy hy0
  have hProf : prolateWKBProfile s y = w / (p * q) := by
    rw [prolateWKBProfile_eq_div hsy.le, hwdef, hpdef, hqdef, ← Real.sqrt_mul (by linarith)]
    ring_nf
  have hlb : r * w * p ≤ bandEndpointPhase s y := by
    have h := sharp_le_bandEndpointPhase (s := s) hy0.le hy1.le
    calc r * w * p = Real.sqrt (y ^ 2 - s) * Real.sqrt (2 * (1 - y)) := by
          rw [hwdef, hrdef, hpdef, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
          ring
      _ ≤ bandEndpointPhase s y := h
  have hquot : prolateWKBProfile s y / bandEndpointPhase s y ≤ 1 / (r * p ^ 2 * q) := by
    rw [hProf, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hlb (mul_pos hp hq).le, hp2]
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have hden : (0 : ℝ) < r * (1 - y) * q := by positivity
  have hsplit : y / (1 - y ^ 2) - 1 / (r * (1 - y) * q)
      = (y * (r * (1 - y) * q) - (1 - y ^ 2) * 1) / ((1 - y ^ 2) * (r * (1 - y) * q)) :=
    div_sub_div _ _ (ne_of_gt h1y2) (ne_of_gt hden)
  have hkey : -2 * ((1 - y ^ 2) * (r * (1 - y) * q))
      ≤ y * (r * (1 - y) * q) - (1 - y ^ 2) * 1 := by
    have hcore : q ≤ r * (y + 2 - 2 * y ^ 2) := by nlinarith [hqr, hr, hy0, hy1]
    have hmul : q * q ≤ r * (y + 2 - 2 * y ^ 2) * q :=
      mul_le_mul_of_nonneg_right hcore hq.le
    nlinarith [hmul, hq2, hy1, hr, hq]
  have hstep : -2 ≤ y / (1 - y ^ 2) - 1 / (r * p ^ 2 * q) := by
    rw [hp2, hsplit, le_div_iff₀ (by positivity)]
    linarith [hkey]
  rw [bandPhaseLogDefect, neg_div]
  linarith [hquot, hstep]

/-- **The defect is bounded by two**, uniformly in the separation parameter and up to the
endpoint. -/
theorem abs_bandPhaseLogDefect_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hy0 : 0 < y) (hy1 : y < 1) (hsy : s < y ^ 2) :
    |bandPhaseLogDefect s y| ≤ 2 :=
  abs_le.2 ⟨le_bandPhaseLogDefect hy0 hy1 hsy, bandPhaseLogDefect_le hs0 hs1 hy0 hy1 hsy⟩

end

end GaloisForLFunctions.RHTower

end
