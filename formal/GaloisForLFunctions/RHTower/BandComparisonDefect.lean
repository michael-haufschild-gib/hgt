import GaloisForLFunctions.RHTower.BandPhaseLogDefect

/-!
# The comparison defect of the prolate band is a simple pole

The band equation and its modified-Bessel comparison model share the aperture term exactly, so their
difference is the defect

```text
a = 1/(1-y²)² + B²/4 + B'/2 ,      B = Xi'/Xi - Xi''/Xi' ,
```

which contains no `c` at all.  Each of the four terms is a double pole at the endpoint — with
coefficients `1`, `-1/16`, `-1/4`, `1/4` and `1/16` after expansion — and they cancel: writing
`Xi'/Xi = -y/(1-y²) + L` splits `a` into an explicit rational function

```text
(y⁴ + (3-8s) y² + 2s² + 2s) / (4 (1-y²) (y²-s)²) ,
```

a *simple* pole, plus two terms each carrying a factor of the bounded quantity `L`.  The double poles
cancel inside the rational part, which is why its numerator is divisible by `1-y²`.

The resulting bound `|a| ≤ 100/(1-y²)` is uniform in the aperture and holds on the endpoint collar
`1/2 ≤ y < 1` for every separation parameter `s ≤ 1/8`.  A simple pole is exactly what the Liouville
measure of the band, which vanishes like `sqrt(1-y)` at the endpoint, can integrate.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The derivative of the model drift `Xi''/Xi'` of the band. -/
def bandModelDriftDeriv (s y : ℝ) : ℝ :=
  (1 - s) * (3 * y ^ 4 - (1 + s) * y ^ 2 - s) / ((1 - y ^ 2) ^ 2 * (y ^ 2 - s) ^ 2)

/-- The first-order coefficient of the band comparison equation, `Xi'/Xi - Xi''/Xi'`. -/
def bandFirstOrderCoeff (s y : ℝ) : ℝ :=
  -(prolateWKBProfile s y) / bandEndpointPhase s y - bandModelDrift s y

/-- Its derivative. -/
def bandFirstOrderCoeffDeriv (s y : ℝ) : ℝ :=
  -(prolateWKBProfile s y) * bandModelDrift s y / bandEndpointPhase s y
    - prolateWKBProfile s y ^ 2 / bandEndpointPhase s y ^ 2 - bandModelDriftDeriv s y

/-- The comparison defect of the band against its modified-Bessel model. -/
def bandComparisonDefect (s y : ℝ) : ℝ :=
  1 / (1 - y ^ 2) ^ 2 + bandFirstOrderCoeff s y ^ 2 / 4 + bandFirstOrderCoeffDeriv s y / 2

/-- The rational part of the defect, after the endpoint double poles have cancelled. -/
def bandDefectAlg (s y : ℝ) : ℝ :=
  (y ^ 4 + (3 - 8 * s) * y ^ 2 + 2 * s ^ 2 + 2 * s) / (4 * (1 - y ^ 2) * (y ^ 2 - s) ^ 2)

section

variable {s y : ℝ}

/-- The derivative of the model drift. -/
theorem hasDerivAt_bandModelDrift (hy : (1 : ℝ) - y ^ 2 ≠ 0) (hys : y ^ 2 - s ≠ 0) :
    HasDerivAt (bandModelDrift s) (bandModelDriftDeriv s y) y := by
  have hden : (1 - y ^ 2) * (y ^ 2 - s) ≠ 0 := mul_ne_zero hy hys
  have hnum : HasDerivAt (fun t : ℝ => t * (1 - s)) (1 - s) y := by
    refine ((hasDerivAt_id y).mul_const (1 - s)).congr_deriv ?_
    ring
  have hd : HasDerivAt (fun t : ℝ => (1 - t ^ 2) * (t ^ 2 - s))
      (-(2 * y) * (y ^ 2 - s) + (1 - y ^ 2) * (2 * y)) y := by
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
      refine ((hasDerivAt_pow 2 y).const_sub 1).congr_deriv ?_
      ring
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 - s) (2 * y) y := by
      refine ((hasDerivAt_pow 2 y).sub_const s).congr_deriv ?_
      ring
    exact h1.fun_mul h2
  have hfun : bandModelDrift s = fun t : ℝ => t * (1 - s) / ((1 - t ^ 2) * (t ^ 2 - s)) := by
    funext t
    rw [bandModelDrift]
  rw [hfun]
  refine (hnum.fun_div hd hden).congr_deriv ?_
  rw [bandModelDriftDeriv]
  field_simp
  ring

/-- **The defect splits into a simple pole plus bounded corrections.**  The endpoint double poles
cancel identically; `P` and `Xi` survive only inside the bounded logarithmic defect. -/
theorem bandComparisonDefect_eq (hy : (1 : ℝ) - y ^ 2 ≠ 0) (hys : y ^ 2 - s ≠ 0)
    (hXi : bandEndpointPhase s y ≠ 0) :
    bandComparisonDefect s y
      = bandDefectAlg s y + y * bandPhaseLogDefect s y / (2 * (1 - y ^ 2))
        - bandPhaseLogDefect s y ^ 2 / 4 := by
  rw [bandComparisonDefect, bandFirstOrderCoeff, bandFirstOrderCoeffDeriv, bandPhaseLogDefect,
    bandDefectAlg, bandModelDrift, bandModelDriftDeriv]
  field_simp
  ring

/-- The rational part is a simple pole with an explicit constant on the endpoint collar. -/
theorem abs_bandDefectAlg_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 ≤ y) (hy1 : y < 1) :
    |bandDefectAlg s y| ≤ 96 / (1 - y ^ 2) := by
  have hy2 : y ^ 2 < 1 := by nlinarith
  have h1y2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  have hys : (1 : ℝ) / 8 ≤ y ^ 2 - s := by nlinarith
  have hnum : |y ^ 4 + (3 - 8 * s) * y ^ 2 + 2 * s ^ 2 + 2 * s| ≤ 6 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg y, sq_nonneg s]
  rw [bandDefectAlg, abs_div, div_le_div_iff₀ (by positivity) h1y2]
  have hden : |4 * (1 - y ^ 2) * (y ^ 2 - s) ^ 2| = 4 * (1 - y ^ 2) * (y ^ 2 - s) ^ 2 :=
    abs_of_pos (by positivity)
  rw [hden]
  have hys2 : (1 : ℝ) / 64 ≤ (y ^ 2 - s) ^ 2 := by nlinarith
  nlinarith [hnum, h1y2, hys2, abs_nonneg (y ^ 4 + (3 - 8 * s) * y ^ 2 + 2 * s ^ 2 + 2 * s),
    mul_nonneg (by nlinarith : (0:ℝ) ≤ 384 * (y ^ 2 - s) ^ 2 - 6) h1y2.le]

/-- **The comparison defect of the band has only a simple pole**, uniformly in the aperture — which
cancels identically — and uniformly in the separation parameter through `s ≤ 1/8` alone. -/
theorem abs_bandComparisonDefect_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 ≤ y)
    (hy1 : y < 1) :
    |bandComparisonDefect s y| ≤ 100 / (1 - y ^ 2) := by
  have hy2 : y ^ 2 < 1 := by nlinarith
  have h1y2 : (0 : ℝ) < 1 - y ^ 2 := by linarith
  have hy1' : (1 : ℝ) - y ^ 2 ≠ 0 := ne_of_gt h1y2
  have hsy : s < y ^ 2 := by nlinarith
  have hys : (y : ℝ) ^ 2 - s ≠ 0 := by
    intro h
    nlinarith
  have hXi : bandEndpointPhase s y ≠ 0 :=
    ne_of_gt (bandEndpointPhase_pos hy1 hsy (by linarith))
  have hL : |bandPhaseLogDefect s y| ≤ 2 :=
    abs_bandPhaseLogDefect_le hs0 (by linarith) (by linarith) hy1 hsy
  have halg : |bandDefectAlg s y| ≤ 96 / (1 - y ^ 2) := abs_bandDefectAlg_le hs0 hs1 hy0 hy1
  have hmid : |y * bandPhaseLogDefect s y / (2 * (1 - y ^ 2))| ≤ 1 / (1 - y ^ 2) := by
    rw [abs_div, div_le_div_iff₀ (by positivity) h1y2]
    have h1 : |y * bandPhaseLogDefect s y| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ y)]
      nlinarith [abs_nonneg (bandPhaseLogDefect s y), hL, hy1]
    have h2 : |2 * (1 - y ^ 2)| = 2 * (1 - y ^ 2) := abs_of_pos (by linarith)
    rw [h2]
    nlinarith [h1, h1y2]
  have hsq : |bandPhaseLogDefect s y ^ 2 / 4| ≤ 3 / (1 - y ^ 2) := by
    have hs2 : bandPhaseLogDefect s y ^ 2 ≤ 4 := by
      nlinarith [abs_nonneg (bandPhaseLogDefect s y), hL, sq_abs (bandPhaseLogDefect s y)]
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
      div_le_div_iff₀ (by norm_num) h1y2]
    nlinarith [hs2, h1y2, hy2, sq_nonneg (bandPhaseLogDefect s y)]
  rw [bandComparisonDefect_eq hy1' hys hXi]
  have htri := abs_sub (bandDefectAlg s y + y * bandPhaseLogDefect s y / (2 * (1 - y ^ 2)))
    (bandPhaseLogDefect s y ^ 2 / 4)
  have htri2 := abs_add_le (bandDefectAlg s y) (y * bandPhaseLogDefect s y / (2 * (1 - y ^ 2)))
  have hsum : (96 : ℝ) / (1 - y ^ 2) + 1 / (1 - y ^ 2) + 3 / (1 - y ^ 2) = 100 / (1 - y ^ 2) := by
    field_simp
    ring
  linarith [htri, htri2, halg, hmid, hsq, hsum]

end

end GaloisForLFunctions.RHTower

end
