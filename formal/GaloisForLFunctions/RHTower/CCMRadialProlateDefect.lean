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

end GaloisForLFunctions.RHTower

end
