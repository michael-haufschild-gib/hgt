import GaloisForLFunctions.RHTower.BandBesselModel

/-!
# The Liouville weight of the band

The integrating factor of the band comparison equation is

```text
m̃ = Ξ / P ,      P = -Ξ' = sqrt((y²-s)/(1-y²)) ,
```

the positive version of `ξ/ξ'`.  It obeys `m̃' = m̃ · B` with `B` the first-order coefficient, which is
the identity that makes the drift Wronskian transport exact, and it vanishes linearly at the
endpoint:

```text
(1-y) ≤ m̃(y) ≤ 6(1-y)      on 1/2 ≤ y ≤ 1,  0 ≤ s ≤ 1/8 .
```

The linear vanishing is what turns the simple pole of the comparison defect into a bounded density:
`m̃ |a| ≤ 600` on the collar.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The Liouville weight of the band, `Ξ/P`. -/
def bandLiouvilleWeight (s y : ℝ) : ℝ :=
  bandEndpointPhase s y / prolateWKBProfile s y

section

variable {s y : ℝ}

theorem prolateWKBProfile_pos (hy : (0 : ℝ) < 1 - y ^ 2) (hys : s < y ^ 2) :
    0 < prolateWKBProfile s y := by
  rw [prolateWKBProfile]
  refine Real.sqrt_pos.2 ?_
  have h1 : (0 : ℝ) < y ^ 2 - s := by linarith
  positivity

theorem bandLiouvilleWeight_pos (hy1 : 0 < y) (hy2 : y < 1) (hys : s < y ^ 2) :
    0 < bandLiouvilleWeight s y := by
  have hy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  exact div_pos (bandEndpointPhase_pos hy2 hys hy1) (prolateWKBProfile_pos hy hys)

/-- **The integrating-factor law.**  `m̃' = m̃ B` with `B` the first-order coefficient of the band
comparison equation. -/
theorem hasDerivAt_bandLiouvilleWeight (hy1 : 0 < y) (hy2 : y < 1) (hys : s < y ^ 2) :
    HasDerivAt (bandLiouvilleWeight s)
      (bandLiouvilleWeight s y * bandFirstOrderCoeff s y) y := by
  have hy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have hP : 0 < prolateWKBProfile s y := prolateWKBProfile_pos hy hys
  have hXi : 0 < bandEndpointPhase s y := bandEndpointPhase_pos hy2 hys hy1
  have hR : (y ^ 2 - s) / (1 - y ^ 2) ≠ 0 := by
    have h1 : (0 : ℝ) < y ^ 2 - s := by linarith
    positivity
  have hXid : HasDerivAt (bandEndpointPhase s) (-(prolateWKBProfile s y)) y :=
    hasDerivAt_bandEndpointPhase (by linarith) hy2 hys.le
  have hPd : HasDerivAt (prolateWKBProfile s)
      (2 * y * (1 - s) / (1 - y ^ 2) ^ 2 / (2 * prolateWKBProfile s y)) y :=
    hasDerivAt_prolateWKBProfile hy.ne' hR
  have hkey : 2 * y * (1 - s) / (1 - y ^ 2) ^ 2 / (2 * prolateWKBProfile s y)
      = prolateWKBProfile s y * bandModelDrift s y := by
    have h := secondDeriv_div_deriv_bandEndpointPhase (s := s) (y := y) hy hys
    field_simp at h ⊢
    linarith [h]
  rw [hkey] at hPd
  have h := hXid.fun_div hPd hP.ne'
  have hval : (-(prolateWKBProfile s y) * prolateWKBProfile s y
        - bandEndpointPhase s y * (prolateWKBProfile s y * bandModelDrift s y))
        / prolateWKBProfile s y ^ 2
      = bandLiouvilleWeight s y * bandFirstOrderCoeff s y := by
    rw [bandLiouvilleWeight, bandFirstOrderCoeff]
    field_simp
  exact h.congr_deriv hval

/-- The weight vanishes at least linearly at the endpoint. -/
theorem one_sub_le_bandLiouvilleWeight (hy0 : 0 ≤ y) (hy2 : y ≤ 1) (hys : s < y ^ 2) :
    1 - y ≤ bandLiouvilleWeight s y := by
  rcases eq_or_lt_of_le hy2 with rfl | hylt
  · have hXi : bandEndpointPhase s 1 = 0 := bandEndpointPhase_one s
    rw [bandLiouvilleWeight, hXi]
    simp
  have hy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  have hP : 0 < prolateWKBProfile s y := prolateWKBProfile_pos hy hys
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
  have hq1 : 1 ≤ q := by nlinarith [hq2, hq, hy0]
  have hr1 : 1 ≤ r := by nlinarith [hr2, hr]
  have hProf : prolateWKBProfile s y = w / (p * q) := by
    rw [prolateWKBProfile_eq_div hys.le, hwdef, hpdef, hqdef, ← Real.sqrt_mul (by linarith)]
    ring_nf
  have hlb : r * w * p ≤ bandEndpointPhase s y := by
    have h := sharp_le_bandEndpointPhase (s := s) hy0 hy2
    calc r * w * p = Real.sqrt (y ^ 2 - s) * Real.sqrt (2 * (1 - y)) := by
          rw [hwdef, hrdef, hpdef, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
          ring
      _ ≤ bandEndpointPhase s y := h
  rw [bandLiouvilleWeight, hProf, div_div_eq_mul_div, le_div_iff₀ hw]
  have h1 : (1 - y) * w ≤ r * w * p * (p * q) := by
    have hrw : r * w * p * (p * q) = r * q * (w * p ^ 2) := by ring
    rw [hrw, hp2]
    nlinarith [mul_nonneg (by nlinarith [hq1, hr1] : (0:ℝ) ≤ r * q - 1)
      (mul_nonneg hw.le (by linarith : (0:ℝ) ≤ 1 - y))]
  have h2 : r * w * p * (p * q) ≤ bandEndpointPhase s y * (p * q) :=
    mul_le_mul_of_nonneg_right hlb (by positivity)
  linarith

/-- The weight vanishes at most linearly at the endpoint, on the collar. -/
theorem bandLiouvilleWeight_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hy0 : 1 / 2 ≤ y) (hy2 : y ≤ 1) :
    bandLiouvilleWeight s y ≤ 6 * (1 - y) := by
  rcases eq_or_lt_of_le hy2 with rfl | hylt
  · have hXi : bandEndpointPhase s 1 = 0 := bandEndpointPhase_one s
    rw [bandLiouvilleWeight, hXi]
    simp
  have hy2' : y ^ 2 < 1 := by nlinarith
  have hy : (0 : ℝ) < 1 - y ^ 2 := by linarith
  have hys : s < y ^ 2 := by nlinarith
  have hP : 0 < prolateWKBProfile s y := prolateWKBProfile_pos hy hys
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
  have hv1 : v ≤ 1 := by nlinarith [hv2, hv, hs0]
  have hy2low : (1 : ℝ) / 4 ≤ y ^ 2 := by nlinarith
  have hwlow : 1 ≤ 3 * w := by nlinarith [hw2, hw, hy2low, hs1]
  have hProf : prolateWKBProfile s y = w / (p * q) := by
    rw [prolateWKBProfile_eq_div hys.le, hwdef, hpdef, hqdef, ← Real.sqrt_mul (by linarith)]
    ring_nf
  have hub : bandEndpointPhase s y ≤ 2 * v * p / q := by
    have h := bandEndpointPhase_le_sharp (s := s) (by linarith) hy2
    calc bandEndpointPhase s y ≤ Real.sqrt (1 - s) *
          (2 * Real.sqrt (1 - y) / Real.sqrt (1 + y)) := h
      _ = 2 * v * p / q := by rw [hvdef, hpdef, hqdef]; ring
  have hub' : bandEndpointPhase s y * q ≤ 2 * v * p := (le_div_iff₀ hq).mp hub
  rw [bandLiouvilleWeight, hProf, div_div_eq_mul_div, div_le_iff₀ hw]
  have hstep : bandEndpointPhase s y * (p * q) ≤ 2 * v * p * p := by
    nlinarith [mul_le_mul_of_nonneg_right hub' hp.le]
  have hrw : 2 * v * p * p = 2 * v * (1 - y) := by
    rw [← hp2]; ring
  rw [hrw] at hstep
  nlinarith [hstep, mul_nonneg (by nlinarith [hv1, hwlow] : (0:ℝ) ≤ 6 * w - 2 * v)
    (by linarith : (0:ℝ) ≤ 1 - y)]

theorem bandLiouvilleWeight_one (s : ℝ) : bandLiouvilleWeight s 1 = 0 := by
  rw [bandLiouvilleWeight, bandEndpointPhase_one, zero_div]

/-! ## The sharp form of the two-sided bound

Both bounds agree to relative order `1-y` at the endpoint; that is what pins the amplitude ratio
`m̃/(1-y²)` to `1` there. -/

theorem sharp_le_bandLiouvilleWeight (hy0 : 0 ≤ y) (hy2 : y ≤ 1) (hys : s < y ^ 2) :
    Real.sqrt 2 * (1 - y) * Real.sqrt (1 + y) ≤ bandLiouvilleWeight s y := by
  rcases eq_or_lt_of_le hy2 with rfl | hylt
  · rw [bandLiouvilleWeight_one]
    simp
  have hy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  set p := Real.sqrt (1 - y) with hpdef
  set q := Real.sqrt (1 + y) with hqdef
  set w := Real.sqrt (y ^ 2 - s) with hwdef
  set r := Real.sqrt 2 with hrdef
  have hp : 0 < p := Real.sqrt_pos.2 (by linarith)
  have hq : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hw : 0 < w := Real.sqrt_pos.2 (by linarith)
  have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hp2 : p ^ 2 = 1 - y := Real.sq_sqrt (by linarith)
  have hProf : prolateWKBProfile s y = w / (p * q) := by
    rw [prolateWKBProfile_eq_div hys.le, hwdef, hpdef, hqdef, ← Real.sqrt_mul (by linarith)]
    ring_nf
  have hlb : r * w * p ≤ bandEndpointPhase s y := by
    have h := sharp_le_bandEndpointPhase (s := s) hy0 hy2
    calc r * w * p = Real.sqrt (y ^ 2 - s) * Real.sqrt (2 * (1 - y)) := by
          rw [hwdef, hrdef, hpdef, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
          ring
      _ ≤ bandEndpointPhase s y := h
  rw [bandLiouvilleWeight, hProf, div_div_eq_mul_div, le_div_iff₀ hw]
  have h2 : r * w * p * (p * q) ≤ bandEndpointPhase s y * (p * q) :=
    mul_le_mul_of_nonneg_right hlb (by positivity)
  have h3 : r * (1 - y) * q * w = r * w * p * (p * q) := by
    rw [← hp2]; ring
  linarith [h2, h3.le, h3.ge]

theorem bandLiouvilleWeight_le_sharp (hy0 : 0 ≤ y) (hy2 : y ≤ 1) (hys : s < y ^ 2) :
    bandLiouvilleWeight s y ≤ 2 * Real.sqrt (1 - s) * (1 - y) / Real.sqrt (y ^ 2 - s) := by
  rcases eq_or_lt_of_le hy2 with rfl | hylt
  · rw [bandLiouvilleWeight_one]
    simp
  have hy : (0 : ℝ) < 1 - y ^ 2 := by nlinarith
  set p := Real.sqrt (1 - y) with hpdef
  set q := Real.sqrt (1 + y) with hqdef
  set w := Real.sqrt (y ^ 2 - s) with hwdef
  set v := Real.sqrt (1 - s) with hvdef
  have hp : 0 < p := Real.sqrt_pos.2 (by linarith)
  have hq : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hw : 0 < w := Real.sqrt_pos.2 (by linarith)
  have hv : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hp2 : p ^ 2 = 1 - y := Real.sq_sqrt (by linarith)
  have hProf : prolateWKBProfile s y = w / (p * q) := by
    rw [prolateWKBProfile_eq_div hys.le, hwdef, hpdef, hqdef, ← Real.sqrt_mul (by linarith)]
    ring_nf
  have hub : bandEndpointPhase s y ≤ 2 * v * p / q := by
    have h := bandEndpointPhase_le_sharp (s := s) hy0 hy2
    calc bandEndpointPhase s y ≤ Real.sqrt (1 - s) *
          (2 * Real.sqrt (1 - y) / Real.sqrt (1 + y)) := h
      _ = 2 * v * p / q := by rw [hvdef, hpdef, hqdef]; ring
  have hub' : bandEndpointPhase s y * q ≤ 2 * v * p := (le_div_iff₀ hq).mp hub
  rw [bandLiouvilleWeight, hProf, div_div_eq_mul_div, div_le_div_iff₀ hw hw]
  have hstep : bandEndpointPhase s y * (p * q) ≤ 2 * v * p * p := by
    nlinarith [mul_le_mul_of_nonneg_right hub' hp.le]
  have hrw : 2 * v * p * p = 2 * v * (1 - y) := by
    rw [← hp2]; ring
  rw [hrw] at hstep
  nlinarith [hstep, hw]

end

end GaloisForLFunctions.RHTower

end
