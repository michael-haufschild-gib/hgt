import GaloisForLFunctions.RHTower.CCMFirstRowDunsterModel
import GaloisForLFunctions.RHTower.CCMFirstRowEnvelopeTail

/-!
# The defect of the radial prolate equation against the pole-uniform comparison equation

The radial prolate equation with separation constant `chi = s c²`,

```text
((x² - 1) R')' - (chi - c² x²) R = 0,      x > 1,
```

has Liouville normal form `u'' + Q u = 0` for `u = sqrt(x² - 1) R`, with

```text
Q(x) = c² (x² - s)/(x² - 1) + 1/(x² - 1)².
```

Its defect against the comparison equation `V'' + P V' + c² (xi')² V = 0` is

```text
a = Q + P²/4 + P'/2 - c² (xi')²,       P = xi'/xi - xi''/xi',
```

and this file computes it exactly and bounds it.  Two facts come out.

* The `c²` terms cancel identically, because `(xi')² = (x² - s)/(x² - 1)`: the defect does not depend on
  the aperture at all.
* The **double pole cancels**, but a simple pole survives:

  ```text
  a = [-(x⁴) + (8s - 3) x² - 2 s (s+1)] / [4 (x² - s)² (x² - 1)]
        - x Δ / (2 (x² - 1)) - Δ²/4,        Δ = xi'/xi - x/(x² - 1),
  ```

  where the first term is an explicit rational function with a simple pole and `Δ` is bounded.  So
  `|a| <= C/(x² - 1)`, not `O(1)`: the `1/(x²-1)²` of the normal form cancels against the double pole of
  `P²/4 + P'/2` exactly, and what is left is the single pole.  This is the pole-uniform property in the
  only form it can hold, and it is the form the Volterra estimate consumes, since the Liouville measure
  `dx / xi'` vanishes to order `sqrt(x² - 1)` at the endpoint.

At `s = 0` everything is elementary and the identity can be read off directly:
`xi_0(x) = sqrt(x² - 1)`, `Δ = 0`, and `a = -(x² + 3)/(4 x² (x² - 1))`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The square of the Liouville speed -/

/-- The Liouville speed squared, with the square root cleared. -/
theorem xiSpeed_sq_mul {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    (x ^ 2 - 1) * xiSpeed s x ^ 2 = x ^ 2 - s := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have h : xiSpeed s x ^ 2 = (x ^ 2 - s) / (x ^ 2 - 1) := by
    rw [xiSpeed]
    exact Real.sq_sqrt (le_of_lt (div_pos hn hd))
  rw [h]
  field_simp

/-! ## The normal-form potential of the radial prolate equation -/

/-- The Liouville normal-form potential of the radial prolate equation with `chi = s c²`. -/
def radialProlateQ (s c x : ℝ) : ℝ := c ^ 2 * ((x ^ 2 - s) / (x ^ 2 - 1)) + 1 / (x ^ 2 - 1) ^ 2

/-- The aperture cancels exactly: the normal-form potential exceeds the comparison potential
`c² (xi')²` by the pure pole `1/(x²-1)²`. -/
theorem radialProlateQ_sub_comparison {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    radialProlateQ s c x - c ^ 2 * xiSpeed s x ^ 2 = 1 / (x ^ 2 - 1) ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hV2 := xiSpeed_sq_mul hs1 hx
  rw [radialProlateQ, ← hV2]
  field_simp
  ring

/-! ## The two logarithmic derivatives of the speed in closed form -/

/-- `xi''/xi'` in closed rational form. -/
theorem xiSpeedDeriv_div_xiSpeed_eq {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiSpeedDeriv s x / xiSpeed s x
      = -(x * (1 - s)) / ((x ^ 2 - s) * (x ^ 2 - 1)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hV2 := xiSpeed_sq_mul hs1 hx
  rw [xiSpeedDeriv, ← hV2]
  field_simp
  ring

/-- `xi'''/xi'` in closed rational form. -/
theorem xiSpeedSecondDeriv_div_xiSpeed_eq {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiSpeedSecondDeriv s x / xiSpeed s x
      = (1 - s) * (x ^ 2 * (4 * (x ^ 2 - s) + s - 1) - (x ^ 2 - s) * (x ^ 2 - 1))
        / ((x ^ 2 - s) * (x ^ 2 - 1)) ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hV2 := xiSpeed_sq_mul hs1 hx
  rw [xiSpeedSecondDeriv, xiSpeedDeriv, ← hV2]
  field_simp
  ring

/-! ## The defect in logarithmic-derivative form -/

/-- **The defect of the radial prolate equation, in logarithmic-derivative form.**  The `c²` terms
cancel identically and what is left involves only the three logarithmic derivatives
`xi'/xi`, `xi''/xi'`, `xi'''/xi'`. -/
theorem lgNormalFormDefect_radialProlate_eq {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 < x) :
    lgNormalFormDefect s c (radialProlateQ s c) x
      = 1 / (x ^ 2 - 1) ^ 2 - (xiSpeed s x / xiEndpointPhase s x) ^ 2 / 4
        + 3 / 4 * (xiSpeedDeriv s x / xiSpeed s x) ^ 2
        - (xiSpeedSecondDeriv s x / xiSpeed s x) / 2 := by
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hQ := radialProlateQ_sub_comparison (s := s) (c := c) hs1 hx
  rw [lgNormalFormDefect, lgFirstOrderCoeff, lgFirstOrderCoeffDeriv]
  have hQ' : radialProlateQ s c x = 1 / (x ^ 2 - 1) ^ 2 + c ^ 2 * xiSpeed s x ^ 2 := by
    linarith [hQ]
  rw [hQ']
  field_simp
  ring

/-! ## The algebraic part and the phase defect -/

/-- The rational part of the defect: the whole defect except for the two terms carrying the
logarithmic derivative of the phase.  Its only pole is simple. -/
def prolateDefectAlg (s x : ℝ) : ℝ :=
  (-(x ^ 4) + (8 * s - 3) * x ^ 2 - 2 * s * (s + 1))
    / (4 * (x ^ 2 - s) ^ 2 * (x ^ 2 - 1))

/-- The deviation of `xi'/xi` from the `s = 0` value `x/(x²-1)`.  It is bounded on the whole ray, and
that is what makes the defect's pole simple. -/
def phaseLogDefect (s x : ℝ) : ℝ :=
  xiSpeed s x / xiEndpointPhase s x - x / (x ^ 2 - 1)

/-- **The defect with its double pole removed.**  The `1/(x²-1)²` of the normal form cancels against
the double pole of `P²/4 + P'/2` exactly, leaving an explicit rational function with a simple pole and
two terms carrying the bounded phase defect. -/
theorem lgNormalFormDefect_radialProlate_eq_alg {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 < x) :
    lgNormalFormDefect s c (radialProlateQ s c) x
      = prolateDefectAlg s x - x * phaseLogDefect s x / (2 * (x ^ 2 - 1))
        - phaseLogDefect s x ^ 2 / 4 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hnu : xiSpeed s x / xiEndpointPhase s x = phaseLogDefect s x + x / (x ^ 2 - 1) := by
    rw [phaseLogDefect]
    ring
  rw [lgNormalFormDefect_radialProlate_eq hs0 hs1 hx, xiSpeedDeriv_div_xiSpeed_eq hs1 hx,
    xiSpeedSecondDeriv_div_xiSpeed_eq hs1 hx, hnu, prolateDefectAlg]
  field_simp
  ring

/-! ## The rational part has a simple pole -/

/-- The rational part of the defect obeys `|a_alg| <= 6/(x²-1)`: its numerator is a quartic and its
denominator carries `(x²-s)² >= x⁴/4`. -/
theorem abs_prolateDefectAlg_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |prolateDefectAlg s x| ≤ 6 / (x ^ 2 - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hden : (0 : ℝ) < 4 * (x ^ 2 - s) ^ 2 * (x ^ 2 - 1) := by positivity
  have hM : |(-(x ^ 4) + (8 * s - 3) * x ^ 2 - 2 * s * (s + 1))| ≤ x ^ 4 + 3 * x ^ 2 + 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg x]
  have hbig : x ^ 4 + 3 * x ^ 2 + 2 ≤ 24 * (x ^ 2 - s) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg x]
  rw [prolateDefectAlg, abs_div, abs_of_pos hden]
  calc |(-(x ^ 4) + (8 * s - 3) * x ^ 2 - 2 * s * (s + 1))| / (4 * (x ^ 2 - s) ^ 2 * (x ^ 2 - 1))
      ≤ (24 * (x ^ 2 - s) ^ 2) / (4 * (x ^ 2 - s) ^ 2 * (x ^ 2 - 1)) := by
        gcongr
        exact le_trans hM hbig
    _ = 6 / (x ^ 2 - 1) := by
        field_simp
        ring


/-! ## The phase defect is bounded

`Δ = xi'/xi - x/(x²-1)` is the only non-algebraic ingredient of the defect.  Away from the endpoint it is
bounded for trivial reasons; near the endpoint the bound is the endpoint bracket `(4)` together with the
`arcosh` comparison, which give the numerator `xi' (x²-1) - x xi` a factor `(x²-1)^{3/2}` — one power more
than the naive size of either term. -/

/-- The Liouville speed with the pole cleared: `xi'(x) (x²-1) = sqrt(x²-s) sqrt(x²-1)`. -/
theorem xiSpeed_mul_sub_one {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiSpeed s x * (x ^ 2 - 1) = Real.sqrt (x ^ 2 - s) * Real.sqrt (x ^ 2 - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  rw [xiSpeed, ← Real.sqrt_mul hn.le,
    show (x ^ 2 - s) * (x ^ 2 - 1) = (x ^ 2 - s) / (x ^ 2 - 1) * (x ^ 2 - 1) ^ 2 by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hd.le]

/-- The phase defect as a single quotient. -/
theorem phaseLogDefect_eq {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    phaseLogDefect s x
      = (Real.sqrt (x ^ 2 - s) * Real.sqrt (x ^ 2 - 1) - x * xiEndpointPhase s x)
        / (xiEndpointPhase s x * (x ^ 2 - 1)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hmul := xiSpeed_mul_sub_one hs1 hx
  rw [phaseLogDefect, ← hmul]
  field_simp

/-- The logarithmic derivative of the phase is at most `sqrt 2 x/(x²-1)`: the speed is at most
`x/sqrt(x²-1)` and the phase at least `sqrt(x²-1)/sqrt 2`. -/
theorem xiSpeed_div_xiEndpointPhase_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiSpeed s x / xiEndpointPhase s x ≤ Real.sqrt 2 * x / (x ^ 2 - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hd
  have hrsq : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt hd.le
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hnum : xiSpeed s x ≤ x / Real.sqrt (x ^ 2 - 1) := by
    have h := xiSpeed_le_xiCompSpeed hs0 hx
    rwa [xiCompSpeed] at h
  have hden : Real.sqrt (x ^ 2 - 1) / Real.sqrt 2 ≤ xiEndpointPhase s x :=
    sqrt_div_sqrt_two_le_xiEndpointPhase hs0 hs1 hx.le
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have e1 : xiSpeed s x / xiEndpointPhase s x
      ≤ (x / Real.sqrt (x ^ 2 - 1)) / xiEndpointPhase s x :=
    div_le_div_of_nonneg_right hnum hph.le
  have e2 : (x / Real.sqrt (x ^ 2 - 1)) / xiEndpointPhase s x
      ≤ (x / Real.sqrt (x ^ 2 - 1)) / (Real.sqrt (x ^ 2 - 1) / Real.sqrt 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have e3 : (x / Real.sqrt (x ^ 2 - 1)) / (Real.sqrt (x ^ 2 - 1) / Real.sqrt 2)
      = Real.sqrt 2 * x / (x ^ 2 - 1) := by
    rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div, Real.mul_self_sqrt hd.le]
    ring
  linarith [e1, e2, e3.le, e3.ge]

/-- Away from the endpoint the phase defect is bounded by `x/(x²-1)`, because both of its two terms
are: the logarithmic derivative is positive and at most `sqrt 2 x/(x²-1)`. -/
theorem abs_phaseLogDefect_le_far {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |phaseLogDefect s x| ≤ x / (x ^ 2 - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hpos : 0 < xiSpeed s x / xiEndpointPhase s x := div_pos hV hph
  have hup := xiSpeed_div_xiEndpointPhase_le hs0 hs1 hx
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hup' : xiSpeed s x / xiEndpointPhase s x ≤ 3 / 2 * x / (x ^ 2 - 1) := by
    refine hup.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hx0.le) hd.le
  rw [phaseLogDefect, abs_le]
  constructor
  · have : (0 : ℝ) < x / (x ^ 2 - 1) := div_pos hx0 hd
    linarith
  · have hhalf : 3 / 2 * x / (x ^ 2 - 1) - x / (x ^ 2 - 1) = x / (2 * (x ^ 2 - 1)) := by
      field_simp
      ring
    have hle : x / (2 * (x ^ 2 - 1)) ≤ x / (x ^ 2 - 1) :=
      div_le_div_of_nonneg_left hx0.le hd (by linarith)
    linarith


set_option maxHeartbeats 1000000 in
/-- The numeric core of the endpoint bound, with every square root replaced by an opaque variable and
its algebraic law: `p² = x²-s`, `q² = 1-s`, `r² = x²-1`, together with the two brackets for the endpoint
logarithm `L` and the phase `X`. -/
private theorem near_defect_numeric {x s p q r L X : ℝ}
    (hx : 1 < x) (hx2 : x ≤ 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hr0 : 0 < r) (hrsq : r * r = x ^ 2 - 1)
    (hp0 : 0 < p) (hpsq : p * p = x ^ 2 - s)
    (hq0 : 0 < q) (hqsq : q * q = 1 - s)
    (hLu : L ≤ r) (hLl : r * (1 - (x ^ 2 - 1) / 6) ≤ L)
    (hXl : q * L ≤ X) (hXu : X ≤ p * L) (hXr : 2 / 3 * r ≤ X) :
    |(p * r - x * X) / (X * (x ^ 2 - 1))| ≤ 2 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by
    linarith [mul_pos (sub_pos.mpr hx) (show (0 : ℝ) < x + 1 by linarith)]
  have hd3 : x ^ 2 - 1 ≤ 3 := by
    linarith [mul_le_mul hx2 hx2 (by linarith) (by norm_num : (0 : ℝ) ≤ 2)]
  have hX0 : 0 < X := lt_of_lt_of_le (by linarith) hXr
  have hp2 : p ≤ 2 := by nlinarith
  have hphalf : 1 / 2 ≤ p := by nlinarith
  have hq1 : q ≤ 1 := by nlinarith
  have hL0 : 0 < L := by nlinarith
  have hprod : (p - x * q) * (p + x * q) = s * (x ^ 2 - 1) := by
    linear_combination hpsq - x ^ 2 * hqsq
  have hpq : p - x * q ≤ x ^ 2 - 1 := by
    nlinarith [hprod, hphalf, mul_nonneg hx0.le hq0.le]
  have hnumU : p * r - x * X ≤ 4 / 3 * (r * (x ^ 2 - 1)) := by
    have s1 : x * (q * L) ≤ x * X := mul_le_mul_of_nonneg_left hXl hx0.le
    have s2 : q * (r * (1 - (x ^ 2 - 1) / 6)) ≤ q * L := mul_le_mul_of_nonneg_left hLl hq0.le
    have s3 : x * (q * (r * (1 - (x ^ 2 - 1) / 6))) ≤ x * (q * L) :=
      mul_le_mul_of_nonneg_left s2 hx0.le
    have s4 : r * (p - x * q) ≤ r * (x ^ 2 - 1) := mul_le_mul_of_nonneg_left hpq hr0.le
    have s5 : x * q ≤ 2 := by nlinarith
    have s6 : x * q * (r * (x ^ 2 - 1) / 6) ≤ 2 * (r * (x ^ 2 - 1) / 6) :=
      mul_le_mul_of_nonneg_right s5 (div_nonneg (mul_nonneg hr0.le hd.le) (by norm_num))
    have c1 : x * (q * (r * (1 - (x ^ 2 - 1) / 6))) ≤ x * X := le_trans s3 s1
    have c3 : p * r - x * (q * (r * (1 - (x ^ 2 - 1) / 6)))
        = r * (p - x * q) + x * q * (r * (x ^ 2 - 1) / 6) := by ring
    have c4 : r * (p - x * q) + x * q * (r * (x ^ 2 - 1) / 6)
        ≤ r * (x ^ 2 - 1) + 2 * (r * (x ^ 2 - 1) / 6) := by linarith
    have c5 : r * (x ^ 2 - 1) + 2 * (r * (x ^ 2 - 1) / 6) ≤ 4 / 3 * (r * (x ^ 2 - 1)) := by
      linarith
    linarith [c1, c3.le, c3.ge, c4, c5]
  have hnumL : -(4 / 3 * (r * (x ^ 2 - 1))) ≤ p * r - x * X := by
    have s1 : x * X ≤ x * (p * L) := mul_le_mul_of_nonneg_left hXu hx0.le
    have s2 : p * L ≤ p * r := mul_le_mul_of_nonneg_left hLu hp0.le
    have s3 : x * (p * L) ≤ x * (p * r) := mul_le_mul_of_nonneg_left s2 hx0.le
    have s4 : x - 1 ≤ (x ^ 2 - 1) / 2 := by nlinarith
    have t1 : p * (r * (x - 1)) ≤ 2 * (r * (x - 1)) :=
      mul_le_mul_of_nonneg_right hp2 (mul_nonneg hr0.le (by linarith))
    have t2 : r * (x - 1) ≤ r * ((x ^ 2 - 1) / 2) := mul_le_mul_of_nonneg_left s4 hr0.le
    have c1 : x * X ≤ x * (p * r) := le_trans s1 s3
    have c3 : p * r - x * (p * r) = -(p * (r * (x - 1))) := by ring
    have c6 : -(2 * (r * ((x ^ 2 - 1) / 2))) ≥ -(4 / 3 * (r * (x ^ 2 - 1))) := by
      linarith [mul_nonneg hr0.le hd.le]
    linarith [c1, c3.le, c3.ge, t1, t2, c6]
  have hkey : |p * r - x * X| ≤ 2 * (X * (x ^ 2 - 1)) := by
    have habs : |p * r - x * X| ≤ 4 / 3 * (r * (x ^ 2 - 1)) := abs_le.mpr ⟨hnumL, hnumU⟩
    have hstep : 4 / 3 * (r * (x ^ 2 - 1)) ≤ 2 * (X * (x ^ 2 - 1)) := by
      linarith [mul_le_mul_of_nonneg_right hXr hd.le]
    linarith
  have hXd : (0 : ℝ) < X * (x ^ 2 - 1) := mul_pos hX0 hd
  rw [abs_div, abs_of_pos hXd]
  calc |p * r - x * X| / (X * (x ^ 2 - 1))
      ≤ 2 * (X * (x ^ 2 - 1)) / (X * (x ^ 2 - 1)) :=
        div_le_div_of_nonneg_right hkey hXd.le
    _ = 2 := by
        field_simp

/-- Near the endpoint the phase defect is bounded by `2`.  The numerator
`xi'(x)(x²-1) - x xi(x) = sqrt(x²-s) sqrt(x²-1) - x xi(x)` is a difference of two quantities of size
`sqrt(1-s) sqrt(x²-1)` whose leading terms cancel: the bracket `(4)` and the `arcosh` comparison give it
the extra factor `x² - 1`, which is exactly the factor the denominator `xi (x²-1)` carries beyond
`sqrt(x²-1)`. -/
theorem abs_phaseLogDefect_le_near {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hx2 : x ≤ 2) : |phaseLogDefect s x| ≤ 2 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hA : (0 : ℝ) < 1 - s := by linarith
  have hconv : Real.sqrt (1 - s) * Real.sqrt (1 + (x ^ 2 - 1) / (1 - s)) = Real.sqrt (x ^ 2 - s) := by
    rw [← Real.sqrt_mul hA.le]
    congr 1
    field_simp
    ring
  have hXu : xiEndpointPhase s x
      ≤ Real.sqrt (x ^ 2 - s) * GaloisForLFunctions.HTGeometry.endpointLog x := by
    have h := xiEndpointPhase_le_sqrt_one_sub_mul_endpointLog hs0 hs1 hx.le
    rwa [hconv] at h
  have hXl : Real.sqrt (1 - s) * GaloisForLFunctions.HTGeometry.endpointLog x
      ≤ xiEndpointPhase s x := sqrt_one_sub_mul_endpointLog_le_xiEndpointPhase hs0 hs1 hx.le
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr0 : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hd
  have hXr : 2 / 3 * Real.sqrt (x ^ 2 - 1) ≤ xiEndpointPhase s x := by
    refine le_trans ?_ (sqrt_div_sqrt_two_le_xiEndpointPhase hs0 hs1 hx.le)
    calc 2 / 3 * Real.sqrt (x ^ 2 - 1) = Real.sqrt (x ^ 2 - 1) / (3 / 2) := by ring
      _ ≤ Real.sqrt (x ^ 2 - 1) / Real.sqrt 2 :=
        div_le_div_of_nonneg_left hr0.le h2pos h2
  rw [phaseLogDefect_eq hs0 hs1 hx]
  exact near_defect_numeric hx hx2 hs0 hs1 hr0 (Real.mul_self_sqrt hd.le)
    (Real.sqrt_pos.mpr hn) (Real.mul_self_sqrt hn.le)
    (Real.sqrt_pos.mpr hA) (Real.mul_self_sqrt hA.le)
    (GaloisForLFunctions.HTGeometry.endpointLog_le_sqrt hx.le)
    (GaloisForLFunctions.HTGeometry.sqrt_mul_one_sub_le_endpointLog hx.le) hXl hXu hXr

/-! ## The defect has only a simple pole -/

private theorem abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a - b - c| ≤ |a - b| + |(-c)| := by
    rw [sub_eq_add_neg (a - b) c]
    exact abs_add_le (a - b) (-c)
  have h2 : |a - b| ≤ |a| + |(-b)| := by
    rw [sub_eq_add_neg a b]
    exact abs_add_le a (-b)
  rw [abs_neg] at h1 h2
  linarith

/-- **The pole-uniform bound on the defect of the radial prolate equation.**  For every aperture `c`,
every `0 <= s <= 1/2` and every `x > 1`,

```text
|Q + P²/4 + P'/2 - c² (xi')²| <= 40/(x² - 1).
```

The bound is independent of `c`: the aperture cancels identically.  The pole is simple, not double —
the `1/(x²-1)²` of the Liouville normal form cancels exactly against the double pole of `P²/4 + P'/2`,
and the surviving `1/(x²-1)` is integrable against the Liouville measure `dx/xi'`, which is what the
Volterra estimate consumes. -/
theorem abs_lgNormalFormDefect_radialProlate_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 < x) :
    |lgNormalFormDefect s c (radialProlateQ s c) x| ≤ 40 / (x ^ 2 - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  rw [lgNormalFormDefect_radialProlate_eq_alg hs0 hs1 hx, le_div_iff₀ hd]
  have htri := abs_sub_sub_le (prolateDefectAlg s x) (x * phaseLogDefect s x / (2 * (x ^ 2 - 1)))
    (phaseLogDefect s x ^ 2 / 4)
  have htrid := mul_le_mul_of_nonneg_right htri hd.le
  have hAd : |prolateDefectAlg s x| * (x ^ 2 - 1) ≤ 6 :=
    (le_div_iff₀ hd).mp (abs_prolateDefectAlg_le hs0 hs1 hx)
  have hBd : |x * phaseLogDefect s x / (2 * (x ^ 2 - 1))| * (x ^ 2 - 1)
      = x * |phaseLogDefect s x| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hx0,
      abs_of_pos (show (0 : ℝ) < 2 * (x ^ 2 - 1) by linarith)]
    field_simp
  have hCd : |phaseLogDefect s x ^ 2 / 4| * (x ^ 2 - 1)
      = phaseLogDefect s x ^ 2 * (x ^ 2 - 1) / 4 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    ring
  have habs0 : (0 : ℝ) ≤ |phaseLogDefect s x| := abs_nonneg _
  have hsq : phaseLogDefect s x ^ 2 = |phaseLogDefect s x| ^ 2 := (sq_abs _).symm
  rcases le_or_gt x 2 with hx2 | hx2
  · have hD := abs_phaseLogDefect_le_near hs0 hs1 hx hx2
    have hd3 : x ^ 2 - 1 ≤ 3 := by nlinarith
    have hB : x * |phaseLogDefect s x| / 2 ≤ 2 := by nlinarith
    have hC : phaseLogDefect s x ^ 2 * (x ^ 2 - 1) / 4 ≤ 3 := by
      rw [hsq]
      nlinarith
    linarith [htrid, hAd, hBd.le, hBd.ge, hCd.le, hCd.ge]
  · have hD := abs_phaseLogDefect_le_far hs0 hs1 hx
    have hDx : |phaseLogDefect s x| * (x ^ 2 - 1) ≤ x := (le_div_iff₀ hd).mp hD
    have hx4 : x ^ 2 ≤ 4 / 3 * (x ^ 2 - 1) := by nlinarith
    have hB : x * |phaseLogDefect s x| / 2 ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hDx hx0.le]
    have hC : phaseLogDefect s x ^ 2 * (x ^ 2 - 1) / 4 ≤ 1 := by
      rw [hsq]
      nlinarith [mul_le_mul_of_nonneg_left hDx habs0]
    linarith [htrid, hAd, hBd.le, hBd.ge, hCd.le, hCd.ge]


/-! ## The radial prolate equation in Liouville normal form

The substitution `u = sqrt(x²-1) R` removes the first-order term of the radial prolate equation.  The
weight and its two derivatives are elementary, and the resulting potential is exactly `radialProlateQ`:
the `-1/w³ R` produced by the second derivative of the weight cancels the `1/(x²-1)²` of the potential,
which is the reason the normal form has a double pole at all. -/

/-- The normal-form weight `sqrt(x²-1)`. -/
def nfWeight (x : ℝ) : ℝ := Real.sqrt (x ^ 2 - 1)

/-- Its derivative `x/sqrt(x²-1)`. -/
def nfWeightDeriv (x : ℝ) : ℝ := x / Real.sqrt (x ^ 2 - 1)

/-- Its second derivative `-1/(x²-1)^{3/2}`. -/
def nfWeightSecondDeriv (x : ℝ) : ℝ := -(1 / ((x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1)))

theorem hasDerivAt_nfWeight {x : ℝ} (hx : 1 < x) :
    HasDerivAt nfWeight (nfWeightDeriv x) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hinner : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 1
  have h := hinner.sqrt hd.ne'
  have hval : 2 * x / (2 * Real.sqrt (x ^ 2 - 1)) = nfWeightDeriv x := by
    rw [nfWeightDeriv]
    have hr : Real.sqrt (x ^ 2 - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
    field_simp
  have hfun : nfWeight = fun t : ℝ => Real.sqrt (t ^ 2 - 1) := by
    funext t
    rw [nfWeight]
  rw [hfun, ← hval]
  exact h

theorem hasDerivAt_nfWeightDeriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt nfWeightDeriv (nfWeightSecondDeriv x) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hd
  have hrsq : Real.sqrt (x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1) = x ^ 2 - 1 :=
    Real.mul_self_sqrt hd.le
  obtain ⟨W, hW0, hWsq, hWeq⟩ : ∃ W : ℝ, 0 < W ∧ W * W = x ^ 2 - 1
      ∧ Real.sqrt (x ^ 2 - 1) = W := ⟨Real.sqrt (x ^ 2 - 1), hr, hrsq, rfl⟩
  have h := (hasDerivAt_id x).fun_div (hasDerivAt_nfWeight hx) (ne_of_gt hr)
  have hfun : nfWeightDeriv = fun t : ℝ => t / nfWeight t := by
    funext t
    rw [nfWeightDeriv, nfWeight]
  have hval : (1 * nfWeight x - x * nfWeightDeriv x) / nfWeight x ^ 2
      = nfWeightSecondDeriv x := by
    have e2 : W * W - x ^ 2 = -1 := by
      rw [hWsq]
      ring
    rw [nfWeight, nfWeightDeriv, nfWeightSecondDeriv, hWeq, ← hWsq]
    field_simp
    linear_combination e2
  rw [hfun, ← hval]
  exact h

/-- The normal-form solution `u = sqrt(x²-1) R`. -/
def prolateNormalFormSol (R : ℝ → ℝ) (x : ℝ) : ℝ := nfWeight x * R x

/-- Its derivative. -/
def prolateNormalFormSolDeriv (R DR : ℝ → ℝ) (x : ℝ) : ℝ :=
  nfWeightDeriv x * R x + nfWeight x * DR x

/-- Its second derivative. -/
def prolateNormalFormSolSecondDeriv (R DR DDR : ℝ → ℝ) (x : ℝ) : ℝ :=
  nfWeightSecondDeriv x * R x + 2 * (nfWeightDeriv x * DR x) + nfWeight x * DDR x

theorem hasDerivAt_prolateNormalFormSol {x : ℝ} {R DR : ℝ → ℝ} (hx : 1 < x)
    (hR : HasDerivAt R (DR x) x) :
    HasDerivAt (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR x) x := by
  have h := (hasDerivAt_nfWeight hx).fun_mul hR
  have hfun : prolateNormalFormSol R = fun t : ℝ => nfWeight t * R t := by
    funext t
    rw [prolateNormalFormSol]
  rw [hfun, prolateNormalFormSolDeriv]
  exact h

theorem hasDerivAt_prolateNormalFormSolDeriv {x : ℝ} {R DR DDR : ℝ → ℝ} (hx : 1 < x)
    (hR : HasDerivAt R (DR x) x) (hDR : HasDerivAt DR (DDR x) x) :
    HasDerivAt (prolateNormalFormSolDeriv R DR) (prolateNormalFormSolSecondDeriv R DR DDR x) x := by
  have h1 := (hasDerivAt_nfWeightDeriv hx).fun_mul hR
  have h2 := (hasDerivAt_nfWeight hx).fun_mul hDR
  have h := h1.fun_add h2
  have hfun : prolateNormalFormSolDeriv R DR
      = fun t : ℝ => nfWeightDeriv t * R t + nfWeight t * DR t := by
    funext t
    rw [prolateNormalFormSolDeriv]
  have hval : nfWeightSecondDeriv x * R x + nfWeightDeriv x * DR x
      + (nfWeightDeriv x * DR x + nfWeight x * DDR x)
      = prolateNormalFormSolSecondDeriv R DR DDR x := by
    rw [prolateNormalFormSolSecondDeriv]
    ring
  rw [hfun, ← hval]
  exact h

/-- **The radial prolate equation in Liouville normal form.**  If `R` solves

```text
(x² - 1) R'' + 2x R' - (s c² - c² x²) R = 0,
```

the radial spheroidal equation with separation constant `chi = s c²`, then `u = sqrt(x²-1) R` solves
`u'' + Q u = 0` with `Q = radialProlateQ s c`.  The identity is exact: the whole expression equals the
radial equation divided by `sqrt(x²-1)`. -/
theorem prolate_normalForm_ode {s c x : ℝ} {R DR DDR : ℝ → ℝ} (hx : 1 < x)
    (hode : (x ^ 2 - 1) * DDR x + 2 * x * DR x - (s * c ^ 2 - c ^ 2 * x ^ 2) * R x = 0) :
    prolateNormalFormSolSecondDeriv R DR DDR x
      + radialProlateQ s c x * prolateNormalFormSol R x = 0 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hd
  have hrsq : Real.sqrt (x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1) = x ^ 2 - 1 :=
    Real.mul_self_sqrt hd.le
  obtain ⟨W, hW0, hWsq, hWeq⟩ : ∃ W : ℝ, 0 < W ∧ W * W = x ^ 2 - 1
      ∧ Real.sqrt (x ^ 2 - 1) = W := ⟨Real.sqrt (x ^ 2 - 1), hr, hrsq, rfl⟩
  have key : prolateNormalFormSolSecondDeriv R DR DDR x
      + radialProlateQ s c x * prolateNormalFormSol R x
      = ((x ^ 2 - 1) * DDR x + 2 * x * DR x - (s * c ^ 2 - c ^ 2 * x ^ 2) * R x) / W := by
    rw [prolateNormalFormSolSecondDeriv, prolateNormalFormSol, radialProlateQ, nfWeight,
      nfWeightDeriv, nfWeightSecondDeriv, hWeq, ← hWsq]
    field_simp
    ring
  rw [key, hode, zero_div]



/-! ## From the normal form to the comparison equation

The comparison amplitude is `g = sqrt(m) = sqrt(xi/xi')`, whose logarithmic derivative is `P/2` by the
integrating-factor law.  Dividing a solution of the normal form by `g` therefore produces a solution of
the comparison equation, with the defect `Q + P²/4 + P'/2 - c²(xi')²` — which is exactly
`lgNormalFormDefect`. -/

/-- The comparison amplitude `g = sqrt(xi/xi')`. -/
def lgAmplitude (s x : ℝ) : ℝ := Real.sqrt (lgWeight s x)

/-- Its derivative `g P/2`. -/
def lgAmplitudeDeriv (s x : ℝ) : ℝ := lgAmplitude s x * lgFirstOrderCoeff s x / 2

/-- Its second derivative `g (P²/4 + P'/2)`. -/
def lgAmplitudeSecondDeriv (s x : ℝ) : ℝ :=
  lgAmplitude s x * (lgFirstOrderCoeff s x ^ 2 / 4 + lgFirstOrderCoeffDeriv s x / 2)

theorem lgWeight_pos {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) : 0 < lgWeight s x := by
  rw [lgWeight]
  exact div_pos (xiEndpointPhase_pos hs0 hs1 hx) (xiSpeed_pos hs1 hx)

theorem lgAmplitude_pos {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    0 < lgAmplitude s x := by
  rw [lgAmplitude]
  exact Real.sqrt_pos.mpr (lgWeight_pos hs0 hs1 hx)

theorem hasDerivAt_lgAmplitude {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (lgAmplitude s) (lgAmplitudeDeriv s x) x := by
  have hm : 0 < lgWeight s x := lgWeight_pos hs0 hs1 hx
  obtain ⟨G, hG0, hGsq, hGeq⟩ : ∃ G : ℝ, 0 < G ∧ G * G = lgWeight s x
      ∧ Real.sqrt (lgWeight s x) = G :=
    ⟨Real.sqrt (lgWeight s x), Real.sqrt_pos.mpr hm, Real.mul_self_sqrt hm.le, rfl⟩
  have h := (hasDerivAt_lgWeight hs0 hs1 hx).sqrt hm.ne'
  have hval : lgWeight s x * lgFirstOrderCoeff s x / (2 * Real.sqrt (lgWeight s x))
      = lgAmplitudeDeriv s x := by
    rw [lgAmplitudeDeriv, lgAmplitude, hGeq, ← hGsq]
    field_simp
  have hfun : lgAmplitude s = fun t : ℝ => Real.sqrt (lgWeight s t) := by
    funext t
    rw [lgAmplitude]
  rw [hfun, ← hval]
  exact h

theorem hasDerivAt_lgAmplitudeDeriv {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (lgAmplitudeDeriv s) (lgAmplitudeSecondDeriv s x) x := by
  have hg := hasDerivAt_lgAmplitude hs0 hs1 hx
  have hP := hasDerivAt_lgFirstOrderCoeff hs0 hs1 hx
  have h := (hg.fun_mul hP).div_const 2
  have hfun : lgAmplitudeDeriv s
      = fun t : ℝ => lgAmplitude s t * lgFirstOrderCoeff s t / 2 := by
    funext t
    rw [lgAmplitudeDeriv]
  have hval : (lgAmplitudeDeriv s x * lgFirstOrderCoeff s x
        + lgAmplitude s x * lgFirstOrderCoeffDeriv s x) / 2
      = lgAmplitudeSecondDeriv s x := by
    rw [lgAmplitudeSecondDeriv, lgAmplitudeDeriv]
    ring
  rw [hfun, ← hval]
  exact h

/-- The comparison solution `U = u/g` attached to a solution `u` of the normal form. -/
def comparisonSol (u : ℝ → ℝ) (s x : ℝ) : ℝ := u x / lgAmplitude s x

/-- Its derivative. -/
def comparisonSolDeriv (u Du : ℝ → ℝ) (s x : ℝ) : ℝ :=
  (Du x * lgAmplitude s x - u x * lgAmplitudeDeriv s x)
    / (lgAmplitude s x * lgAmplitude s x)

theorem hasDerivAt_comparisonSol {s x : ℝ} {u Du : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 < x) (hu : HasDerivAt u (Du x) x) :
    HasDerivAt (comparisonSol u s) (comparisonSolDeriv u Du s x) x := by
  have hg := hasDerivAt_lgAmplitude hs0 hs1 hx
  have hgpos := lgAmplitude_pos hs0 hs1 hx
  have h := hu.fun_div hg hgpos.ne'
  have hfun : comparisonSol u s = fun t : ℝ => u t / lgAmplitude s t := by
    funext t
    rw [comparisonSol]
  have hval : (Du x * lgAmplitude s x - u x * lgAmplitudeDeriv s x) / lgAmplitude s x ^ 2
      = comparisonSolDeriv u Du s x := by
    rw [comparisonSolDeriv]
    ring
  rw [hfun, ← hval]
  exact h

/-- **A solution of the normal form solves the comparison equation with defect
`lgNormalFormDefect`.**  If `u'' + Q u = 0` at `x`, then `U = u/g` satisfies

```text
U'' = -P U' - (c² (xi')² + a) U,       a = Q + P²/4 + P'/2 - c² (xi')²,
```

which is the exact form the Volterra transport law and the pole-uniform estimate consume.  The proof is
the quotient rule twice, together with `g'= gP/2` and `g'' = g(P²/4 + P'/2)`. -/
theorem hasDerivAt_comparisonSolDeriv {s c x : ℝ} {u Du DDu Q : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hu : HasDerivAt u (Du x) x) (hDu : HasDerivAt Du (DDu x) x)
    (hode : DDu x + Q x * u x = 0) :
    HasDerivAt (comparisonSolDeriv u Du s)
      (-(lgFirstOrderCoeff s x) * comparisonSolDeriv u Du s x
        - (c ^ 2 * xiSpeed s x ^ 2 + lgNormalFormDefect s c Q x) * comparisonSol u s x) x := by
  have hg := hasDerivAt_lgAmplitude hs0 hs1 hx
  have hg2 := hasDerivAt_lgAmplitudeDeriv hs0 hs1 hx
  have hgpos := lgAmplitude_pos hs0 hs1 hx
  have hne : lgAmplitude s x * lgAmplitude s x ≠ 0 := ne_of_gt (mul_pos hgpos hgpos)
  have hDDu : DDu x = -(Q x * u x) := by linarith
  have hfun : comparisonSolDeriv u Du s
      = fun t : ℝ => (Du t * lgAmplitude s t - u t * lgAmplitudeDeriv s t)
          / (lgAmplitude s t * lgAmplitude s t) := by
    funext t
    rw [comparisonSolDeriv]
  rw [hfun]
  refine (((hDu.fun_mul hg).fun_sub (hu.fun_mul hg2)).fun_div (hg.fun_mul hg) hne).congr_deriv ?_
  simp only [comparisonSol, lgNormalFormDefect, lgAmplitudeSecondDeriv, lgAmplitudeDeriv, hDDu]
  field_simp
  ring



/-! ## The card's gate: the actual radial mode against the comparison equation -/

/-- **The radial prolate mode solves the pole-uniform comparison equation with a defect that has only a
simple pole.**  Let `R` solve the radial spheroidal equation of order zero,

```text
(x² - 1) R'' + 2x R' - (chi - c² x²) R = 0,        chi = s c²,   0 <= s <= 1/2,
```

at a point `x > 1`.  Put `u = sqrt(x²-1) R` and `U = u/g` with `g = sqrt(xi_s/xi_s')`.  Then `U` solves the
comparison equation of the Bessel model,

```text
U'' = -P U' - (c² (xi')² + a) U,        P = xi'/xi - xi''/xi',
```

with a defect obeying `|a| <= 40/(x²-1)` — uniformly in the aperture `c`, which cancels identically, and
uniformly in the separation constant through `0 <= s <= 1/2` alone.  No asymptotics of the eigenvalue are
used: the separation law is needed only to know that `s` lies in that range.

This is the exact hypothesis of the pole-uniform Volterra estimate
`abs_perturbed_le_lgEnvelope_mul_exp`, whose exponential factor is the total mass of `m |a| E²`; the
Liouville measure `dx/xi'` vanishes like `sqrt(x²-1)` at the endpoint, so a simple pole has finite
mass. -/
theorem radialProlate_comparison_pole_uniform {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hR : HasDerivAt R (DR x) x) (hDR : HasDerivAt DR (DDR x) x)
    (hode : (x ^ 2 - 1) * DDR x + 2 * x * DR x - (s * c ^ 2 - c ^ 2 * x ^ 2) * R x = 0) :
    HasDerivAt (comparisonSol (prolateNormalFormSol R) s)
        (comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x) x
      ∧ HasDerivAt (comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s)
        (-(lgFirstOrderCoeff s x)
            * comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x
          - (c ^ 2 * xiSpeed s x ^ 2 + lgNormalFormDefect s c (radialProlateQ s c) x)
            * comparisonSol (prolateNormalFormSol R) s x) x
      ∧ |lgNormalFormDefect s c (radialProlateQ s c) x| ≤ 40 / (x ^ 2 - 1) := by
  have hu := hasDerivAt_prolateNormalFormSol hx hR
  have hDu := hasDerivAt_prolateNormalFormSolDeriv hx hR hDR
  have hnf := prolate_normalForm_ode (s := s) (c := c) hx hode
  exact ⟨hasDerivAt_comparisonSol hs0 hs1 hx hu,
    hasDerivAt_comparisonSolDeriv hs0 hs1 hx hu hDu hnf,
    abs_lgNormalFormDefect_radialProlate_le hs0 hs1 hx⟩


end GaloisForLFunctions.RHTower

end
