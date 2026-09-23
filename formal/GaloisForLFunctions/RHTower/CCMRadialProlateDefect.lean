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
    (x ^ (2 : ℕ) - 1) * xiSpeed s x ^ (2 : ℕ) = x ^ (2 : ℕ) - s := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have h : xiSpeed s x ^ (2 : ℕ) = (x ^ (2 : ℕ) - s) / (x ^ (2 : ℕ) - 1) := by
    rw [xiSpeed]
    exact Real.sq_sqrt (le_of_lt (div_pos hn hd))
  rw [h]
  field_simp

/-! ## The normal-form potential of the radial prolate equation -/

/-- The Liouville normal-form potential of the radial prolate equation with `chi = s c²`. -/
def radialProlateQ (s c x : ℝ) : ℝ := c ^ (2 : ℕ) * ((x ^ (2 : ℕ) - s) / (x ^ (2 : ℕ) - 1)) + 1 / (x ^ (2 : ℕ) - 1) ^ (2 : ℕ)

/-- The aperture cancels exactly: the normal-form potential exceeds the comparison potential
`c² (xi')²` by the pure pole `1/(x²-1)²`. -/
theorem radialProlateQ_sub_comparison {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    radialProlateQ s c x - c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) = 1 / (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hV2 := xiSpeed_sq_mul hs1 hx
  rw [radialProlateQ, ← hV2]
  field_simp
  ring

/-! ## The two logarithmic derivatives of the speed in closed form -/

/-- `xi''/xi'` in closed rational form. -/
theorem xiSpeedDeriv_div_xiSpeed_eq {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiSpeedDeriv s x / xiSpeed s x
      = -(x * (1 - s)) / ((x ^ (2 : ℕ) - s) * (x ^ (2 : ℕ) - 1)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hV2 := xiSpeed_sq_mul hs1 hx
  rw [xiSpeedDeriv, ← hV2]
  field_simp
  ring

/-- `xi'''/xi'` in closed rational form. -/
theorem xiSpeedSecondDeriv_div_xiSpeed_eq {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiSpeedSecondDeriv s x / xiSpeed s x
      = (1 - s) * (x ^ (2 : ℕ) * (4 * (x ^ (2 : ℕ) - s) + s - 1) - (x ^ (2 : ℕ) - s) * (x ^ (2 : ℕ) - 1))
        / ((x ^ (2 : ℕ) - s) * (x ^ (2 : ℕ) - 1)) ^ (2 : ℕ) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
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
      = 1 / (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) - (xiSpeed s x / xiEndpointPhase s x) ^ (2 : ℕ) / 4
        + 3 / 4 * (xiSpeedDeriv s x / xiSpeed s x) ^ (2 : ℕ)
        - (xiSpeedSecondDeriv s x / xiSpeed s x) / 2 := by
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hQ := radialProlateQ_sub_comparison (s := s) (c := c) hs1 hx
  rw [lgNormalFormDefect, lgFirstOrderCoeff, lgFirstOrderCoeffDeriv]
  have hQ' : radialProlateQ s c x = 1 / (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) + c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) := by
    linarith [hQ]
  rw [hQ']
  field_simp
  ring

/-! ## The algebraic part and the phase defect -/

/-- The rational part of the defect: the whole defect except for the two terms carrying the
logarithmic derivative of the phase.  Its only pole is simple. -/
def prolateDefectAlg (s x : ℝ) : ℝ :=
  (-(x ^ (4 : ℕ)) + (8 * s - 3) * x ^ (2 : ℕ) - 2 * s * (s + 1))
    / (4 * (x ^ (2 : ℕ) - s) ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1))

/-- The deviation of `xi'/xi` from the `s = 0` value `x/(x²-1)`.  It is bounded on the whole ray, and
that is what makes the defect's pole simple. -/
def phaseLogDefect (s x : ℝ) : ℝ :=
  xiSpeed s x / xiEndpointPhase s x - x / (x ^ (2 : ℕ) - 1)

/-- **The defect with its double pole removed.**  The `1/(x²-1)²` of the normal form cancels against
the double pole of `P²/4 + P'/2` exactly, leaving an explicit rational function with a simple pole and
two terms carrying the bounded phase defect. -/
theorem lgNormalFormDefect_radialProlate_eq_alg {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 < x) :
    lgNormalFormDefect s c (radialProlateQ s c) x
      = prolateDefectAlg s x - x * phaseLogDefect s x / (2 * (x ^ (2 : ℕ) - 1))
        - phaseLogDefect s x ^ (2 : ℕ) / 4 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hnu : xiSpeed s x / xiEndpointPhase s x = phaseLogDefect s x + x / (x ^ (2 : ℕ) - 1) := by
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
    |prolateDefectAlg s x| ≤ 6 / (x ^ (2 : ℕ) - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : (1 : ℝ) ≤ x ^ (2 : ℕ) := by nlinarith
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hden : (0 : ℝ) < 4 * (x ^ (2 : ℕ) - s) ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) := by positivity
  have hM : |(-(x ^ (4 : ℕ)) + (8 * s - 3) * x ^ (2 : ℕ) - 2 * s * (s + 1))| ≤ x ^ (4 : ℕ) + 3 * x ^ (2 : ℕ) + 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg x]
  have hbig : x ^ (4 : ℕ) + 3 * x ^ (2 : ℕ) + 2 ≤ 24 * (x ^ (2 : ℕ) - s) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x ^ (2 : ℕ) - 1), sq_nonneg x]
  rw [prolateDefectAlg, abs_div, abs_of_pos hden]
  calc |(-(x ^ (4 : ℕ)) + (8 * s - 3) * x ^ (2 : ℕ) - 2 * s * (s + 1))| / (4 * (x ^ (2 : ℕ) - s) ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1))
      ≤ (24 * (x ^ (2 : ℕ) - s) ^ (2 : ℕ)) / (4 * (x ^ (2 : ℕ) - s) ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1)) := by
        gcongr
        exact le_trans hM hbig
    _ = 6 / (x ^ (2 : ℕ) - 1) := by
        field_simp
        ring


/-! ## The phase defect is bounded

`Δ = xi'/xi - x/(x²-1)` is the only non-algebraic ingredient of the defect.  Away from the endpoint it is
bounded for trivial reasons; near the endpoint the bound is the endpoint bracket `(4)` together with the
`arcosh` comparison, which give the numerator `xi' (x²-1) - x xi` a factor `(x²-1)^{3/2}` — one power more
than the naive size of either term. -/

/-- The Liouville speed with the pole cleared: `xi'(x) (x²-1) = sqrt(x²-s) sqrt(x²-1)`. -/
theorem xiSpeed_mul_sub_one {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiSpeed s x * (x ^ (2 : ℕ) - 1) = Real.sqrt (x ^ (2 : ℕ) - s) * Real.sqrt (x ^ (2 : ℕ) - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  rw [xiSpeed, ← Real.sqrt_mul hn.le,
    show (x ^ (2 : ℕ) - s) * (x ^ (2 : ℕ) - 1) = (x ^ (2 : ℕ) - s) / (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hd.le]

/-- The phase defect as a single quotient. -/
theorem phaseLogDefect_eq {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    phaseLogDefect s x
      = (Real.sqrt (x ^ (2 : ℕ) - s) * Real.sqrt (x ^ (2 : ℕ) - 1) - x * xiEndpointPhase s x)
        / (xiEndpointPhase s x * (x ^ (2 : ℕ) - 1)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hmul := xiSpeed_mul_sub_one hs1 hx
  rw [phaseLogDefect, ← hmul]
  field_simp

/-- The logarithmic derivative of the phase is at most `sqrt 2 x/(x²-1)`: the speed is at most
`x/sqrt(x²-1)` and the phase at least `sqrt(x²-1)/sqrt 2`. -/
theorem xiSpeed_div_xiEndpointPhase_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiSpeed s x / xiEndpointPhase s x ≤ Real.sqrt 2 * x / (x ^ (2 : ℕ) - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hrsq : Real.sqrt (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := Real.sq_sqrt hd.le
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hnum : xiSpeed s x ≤ x / Real.sqrt (x ^ (2 : ℕ) - 1) := by
    have h := xiSpeed_le_xiCompSpeed hs0 hx
    rwa [xiCompSpeed] at h
  have hden : Real.sqrt (x ^ (2 : ℕ) - 1) / Real.sqrt 2 ≤ xiEndpointPhase s x :=
    sqrt_div_sqrt_two_le_xiEndpointPhase hs0 hs1 hx.le
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have e1 : xiSpeed s x / xiEndpointPhase s x
      ≤ (x / Real.sqrt (x ^ (2 : ℕ) - 1)) / xiEndpointPhase s x :=
    div_le_div_of_nonneg_right hnum hph.le
  have e2 : (x / Real.sqrt (x ^ (2 : ℕ) - 1)) / xiEndpointPhase s x
      ≤ (x / Real.sqrt (x ^ (2 : ℕ) - 1)) / (Real.sqrt (x ^ (2 : ℕ) - 1) / Real.sqrt 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have e3 : (x / Real.sqrt (x ^ (2 : ℕ) - 1)) / (Real.sqrt (x ^ (2 : ℕ) - 1) / Real.sqrt 2)
      = Real.sqrt 2 * x / (x ^ (2 : ℕ) - 1) := by
    rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div, Real.mul_self_sqrt hd.le]
    ring
  linarith [e1, e2, e3.le, e3.ge]

/-- Away from the endpoint the phase defect is bounded by `x/(x²-1)`, because both of its two terms
are: the logarithmic derivative is positive and at most `sqrt 2 x/(x²-1)`. -/
theorem abs_phaseLogDefect_le_far {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |phaseLogDefect s x| ≤ x / (x ^ (2 : ℕ) - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hpos : 0 < xiSpeed s x / xiEndpointPhase s x := div_pos hV hph
  have hup := xiSpeed_div_xiEndpointPhase_le hs0 hs1 hx
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ (2 : ℕ)) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hup' : xiSpeed s x / xiEndpointPhase s x ≤ 3 / 2 * x / (x ^ (2 : ℕ) - 1) := by
    refine hup.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hx0.le) hd.le
  rw [phaseLogDefect, abs_le]
  constructor
  · have : (0 : ℝ) < x / (x ^ (2 : ℕ) - 1) := div_pos hx0 hd
    linarith
  · have hhalf : 3 / 2 * x / (x ^ (2 : ℕ) - 1) - x / (x ^ (2 : ℕ) - 1) = x / (2 * (x ^ (2 : ℕ) - 1)) := by
      field_simp
      ring
    have hle : x / (2 * (x ^ (2 : ℕ) - 1)) ≤ x / (x ^ (2 : ℕ) - 1) :=
      div_le_div_of_nonneg_left hx0.le hd (by linarith)
    linarith


set_option maxHeartbeats 1000000 in
/-- The numeric core of the endpoint bound, with every square root replaced by an opaque variable and
its algebraic law: `p² = x²-s`, `q² = 1-s`, `r² = x²-1`, together with the two brackets for the endpoint
logarithm `L` and the phase `X`. -/
private theorem near_defect_numeric {x s p q r L X : ℝ}
    (hx : 1 < x) (hx2 : x ≤ 2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hr0 : 0 < r) (hrsq : r * r = x ^ (2 : ℕ) - 1)
    (hp0 : 0 < p) (hpsq : p * p = x ^ (2 : ℕ) - s)
    (hq0 : 0 < q) (hqsq : q * q = 1 - s)
    (hLu : L ≤ r) (hLl : r * (1 - (x ^ (2 : ℕ) - 1) / 6) ≤ L)
    (hXl : q * L ≤ X) (hXu : X ≤ p * L) (hXr : 2 / 3 * r ≤ X) :
    |(p * r - x * X) / (X * (x ^ (2 : ℕ) - 1))| ≤ 2 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by
    linarith [mul_pos (sub_pos.mpr hx) (show (0 : ℝ) < x + 1 by linarith)]
  have hd3 : x ^ (2 : ℕ) - 1 ≤ 3 := by
    linarith [mul_le_mul hx2 hx2 (by linarith) (by norm_num : (0 : ℝ) ≤ 2)]
  have hX0 : 0 < X := lt_of_lt_of_le (by linarith) hXr
  have hp2 : p ≤ 2 := by nlinarith
  have hphalf : 1 / 2 ≤ p := by nlinarith
  have hq1 : q ≤ 1 := by nlinarith
  have hL0 : 0 < L := by nlinarith
  have hprod : (p - x * q) * (p + x * q) = s * (x ^ (2 : ℕ) - 1) := by
    linear_combination hpsq - x ^ (2 : ℕ) * hqsq
  have hpq : p - x * q ≤ x ^ (2 : ℕ) - 1 := by
    nlinarith [hprod, hphalf, mul_nonneg hx0.le hq0.le]
  have hnumU : p * r - x * X ≤ 4 / 3 * (r * (x ^ (2 : ℕ) - 1)) := by
    have s1 : x * (q * L) ≤ x * X := mul_le_mul_of_nonneg_left hXl hx0.le
    have s2 : q * (r * (1 - (x ^ (2 : ℕ) - 1) / 6)) ≤ q * L := mul_le_mul_of_nonneg_left hLl hq0.le
    have s3 : x * (q * (r * (1 - (x ^ (2 : ℕ) - 1) / 6))) ≤ x * (q * L) :=
      mul_le_mul_of_nonneg_left s2 hx0.le
    have s4 : r * (p - x * q) ≤ r * (x ^ (2 : ℕ) - 1) := mul_le_mul_of_nonneg_left hpq hr0.le
    have s5 : x * q ≤ 2 := by nlinarith
    have s6 : x * q * (r * (x ^ (2 : ℕ) - 1) / 6) ≤ 2 * (r * (x ^ (2 : ℕ) - 1) / 6) :=
      mul_le_mul_of_nonneg_right s5 (div_nonneg (mul_nonneg hr0.le hd.le) (by norm_num))
    have c1 : x * (q * (r * (1 - (x ^ (2 : ℕ) - 1) / 6))) ≤ x * X := le_trans s3 s1
    have c3 : p * r - x * (q * (r * (1 - (x ^ (2 : ℕ) - 1) / 6)))
        = r * (p - x * q) + x * q * (r * (x ^ (2 : ℕ) - 1) / 6) := by ring
    have c4 : r * (p - x * q) + x * q * (r * (x ^ (2 : ℕ) - 1) / 6)
        ≤ r * (x ^ (2 : ℕ) - 1) + 2 * (r * (x ^ (2 : ℕ) - 1) / 6) := by linarith
    have c5 : r * (x ^ (2 : ℕ) - 1) + 2 * (r * (x ^ (2 : ℕ) - 1) / 6) ≤ 4 / 3 * (r * (x ^ (2 : ℕ) - 1)) := by
      linarith
    linarith [c1, c3.le, c3.ge, c4, c5]
  have hnumL : -(4 / 3 * (r * (x ^ (2 : ℕ) - 1))) ≤ p * r - x * X := by
    have s1 : x * X ≤ x * (p * L) := mul_le_mul_of_nonneg_left hXu hx0.le
    have s2 : p * L ≤ p * r := mul_le_mul_of_nonneg_left hLu hp0.le
    have s3 : x * (p * L) ≤ x * (p * r) := mul_le_mul_of_nonneg_left s2 hx0.le
    have s4 : x - 1 ≤ (x ^ (2 : ℕ) - 1) / 2 := by nlinarith
    have t1 : p * (r * (x - 1)) ≤ 2 * (r * (x - 1)) :=
      mul_le_mul_of_nonneg_right hp2 (mul_nonneg hr0.le (by linarith))
    have t2 : r * (x - 1) ≤ r * ((x ^ (2 : ℕ) - 1) / 2) := mul_le_mul_of_nonneg_left s4 hr0.le
    have c1 : x * X ≤ x * (p * r) := le_trans s1 s3
    have c3 : p * r - x * (p * r) = -(p * (r * (x - 1))) := by ring
    have c6 : -(2 * (r * ((x ^ (2 : ℕ) - 1) / 2))) ≥ -(4 / 3 * (r * (x ^ (2 : ℕ) - 1))) := by
      linarith [mul_nonneg hr0.le hd.le]
    linarith [c1, c3.le, c3.ge, t1, t2, c6]
  have hkey : |p * r - x * X| ≤ 2 * (X * (x ^ (2 : ℕ) - 1)) := by
    have habs : |p * r - x * X| ≤ 4 / 3 * (r * (x ^ (2 : ℕ) - 1)) := abs_le.mpr ⟨hnumL, hnumU⟩
    have hstep : 4 / 3 * (r * (x ^ (2 : ℕ) - 1)) ≤ 2 * (X * (x ^ (2 : ℕ) - 1)) := by
      linarith [mul_le_mul_of_nonneg_right hXr hd.le]
    linarith
  have hXd : (0 : ℝ) < X * (x ^ (2 : ℕ) - 1) := mul_pos hX0 hd
  rw [abs_div, abs_of_pos hXd]
  calc |p * r - x * X| / (X * (x ^ (2 : ℕ) - 1))
      ≤ 2 * (X * (x ^ (2 : ℕ) - 1)) / (X * (x ^ (2 : ℕ) - 1)) :=
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
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hA : (0 : ℝ) < 1 - s := by linarith
  have hconv : Real.sqrt (1 - s) * Real.sqrt (1 + (x ^ (2 : ℕ) - 1) / (1 - s)) = Real.sqrt (x ^ (2 : ℕ) - s) := by
    rw [← Real.sqrt_mul hA.le]
    congr 1
    field_simp
    ring
  have hXu : xiEndpointPhase s x
      ≤ Real.sqrt (x ^ (2 : ℕ) - s) * GaloisForLFunctions.HTGeometry.endpointLog x := by
    have h := xiEndpointPhase_le_sqrt_one_sub_mul_endpointLog hs0 hs1 hx.le
    rwa [hconv] at h
  have hXl : Real.sqrt (1 - s) * GaloisForLFunctions.HTGeometry.endpointLog x
      ≤ xiEndpointPhase s x := sqrt_one_sub_mul_endpointLog_le_xiEndpointPhase hs0 hs1 hx.le
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ (2 : ℕ)) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr0 : 0 < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hXr : 2 / 3 * Real.sqrt (x ^ (2 : ℕ) - 1) ≤ xiEndpointPhase s x := by
    refine le_trans ?_ (sqrt_div_sqrt_two_le_xiEndpointPhase hs0 hs1 hx.le)
    calc 2 / 3 * Real.sqrt (x ^ (2 : ℕ) - 1) = Real.sqrt (x ^ (2 : ℕ) - 1) / (3 / 2) := by ring
      _ ≤ Real.sqrt (x ^ (2 : ℕ) - 1) / Real.sqrt 2 :=
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
    |lgNormalFormDefect s c (radialProlateQ s c) x| ≤ 40 / (x ^ (2 : ℕ) - 1) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  rw [lgNormalFormDefect_radialProlate_eq_alg hs0 hs1 hx, le_div_iff₀ hd]
  have htri := abs_sub_sub_le (prolateDefectAlg s x) (x * phaseLogDefect s x / (2 * (x ^ (2 : ℕ) - 1)))
    (phaseLogDefect s x ^ (2 : ℕ) / 4)
  have htrid := mul_le_mul_of_nonneg_right htri hd.le
  have hAd : |prolateDefectAlg s x| * (x ^ (2 : ℕ) - 1) ≤ 6 :=
    (le_div_iff₀ hd).mp (abs_prolateDefectAlg_le hs0 hs1 hx)
  have hBd : |x * phaseLogDefect s x / (2 * (x ^ (2 : ℕ) - 1))| * (x ^ (2 : ℕ) - 1)
      = x * |phaseLogDefect s x| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hx0,
      abs_of_pos (show (0 : ℝ) < 2 * (x ^ (2 : ℕ) - 1) by linarith)]
    field_simp
  have hCd : |phaseLogDefect s x ^ (2 : ℕ) / 4| * (x ^ (2 : ℕ) - 1)
      = phaseLogDefect s x ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) / 4 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    ring
  have habs0 : (0 : ℝ) ≤ |phaseLogDefect s x| := abs_nonneg _
  have hsq : phaseLogDefect s x ^ (2 : ℕ) = |phaseLogDefect s x| ^ (2 : ℕ) := (sq_abs _).symm
  rcases le_or_gt x 2 with hx2 | hx2
  · have hD := abs_phaseLogDefect_le_near hs0 hs1 hx hx2
    have hd3 : x ^ (2 : ℕ) - 1 ≤ 3 := by nlinarith
    have hB : x * |phaseLogDefect s x| / 2 ≤ 2 := by nlinarith
    have hC : phaseLogDefect s x ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) / 4 ≤ 3 := by
      rw [hsq]
      nlinarith
    linarith [htrid, hAd, hBd.le, hBd.ge, hCd.le, hCd.ge]
  · have hD := abs_phaseLogDefect_le_far hs0 hs1 hx
    have hDx : |phaseLogDefect s x| * (x ^ (2 : ℕ) - 1) ≤ x := (le_div_iff₀ hd).mp hD
    have hx4 : x ^ (2 : ℕ) ≤ 4 / 3 * (x ^ (2 : ℕ) - 1) := by nlinarith
    have hB : x * |phaseLogDefect s x| / 2 ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hDx hx0.le]
    have hC : phaseLogDefect s x ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) / 4 ≤ 1 := by
      rw [hsq]
      nlinarith [mul_le_mul_of_nonneg_left hDx habs0]
    linarith [htrid, hAd, hBd.le, hBd.ge, hCd.le, hCd.ge]


/-! ## The radial prolate equation in Liouville normal form

The substitution `u = sqrt(x²-1) R` removes the first-order term of the radial prolate equation.  The
weight and its two derivatives are elementary, and the resulting potential is exactly `radialProlateQ`:
the `-1/w³ R` produced by the second derivative of the weight cancels the `1/(x²-1)²` of the potential,
which is the reason the normal form has a double pole at all. -/

/-- The normal-form weight `sqrt(x²-1)`. -/
def nfWeight (x : ℝ) : ℝ := Real.sqrt (x ^ (2 : ℕ) - 1)

/-- Its derivative `x/sqrt(x²-1)`. -/
def nfWeightDeriv (x : ℝ) : ℝ := x / Real.sqrt (x ^ (2 : ℕ) - 1)

/-- Its second derivative `-1/(x²-1)^{3/2}`. -/
def nfWeightSecondDeriv (x : ℝ) : ℝ := -(1 / ((x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - 1)))

theorem hasDerivAt_nfWeight {x : ℝ} (hx : 1 < x) :
    HasDerivAt nfWeight (nfWeightDeriv x) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hinner : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) - 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 1
  have h := hinner.sqrt hd.ne'
  have hval : 2 * x / (2 * Real.sqrt (x ^ (2 : ℕ) - 1)) = nfWeightDeriv x := by
    rw [nfWeightDeriv]
    have hr : Real.sqrt (x ^ (2 : ℕ) - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
    field_simp
  have hfun : nfWeight = fun t : ℝ => Real.sqrt (t ^ (2 : ℕ) - 1) := by
    funext t
    rw [nfWeight]
  rw [hfun, ← hval]
  exact h

theorem hasDerivAt_nfWeightDeriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt nfWeightDeriv (nfWeightSecondDeriv x) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hrsq : Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - 1) = x ^ (2 : ℕ) - 1 :=
    Real.mul_self_sqrt hd.le
  obtain ⟨W, hW0, hWsq, hWeq⟩ : ∃ W : ℝ, 0 < W ∧ W * W = x ^ (2 : ℕ) - 1
      ∧ Real.sqrt (x ^ (2 : ℕ) - 1) = W := ⟨Real.sqrt (x ^ (2 : ℕ) - 1), hr, hrsq, rfl⟩
  have h := (hasDerivAt_id x).fun_div (hasDerivAt_nfWeight hx) (ne_of_gt hr)
  have hfun : nfWeightDeriv = fun t : ℝ => t / nfWeight t := by
    funext t
    rw [nfWeightDeriv, nfWeight]
  have hval : (1 * nfWeight x - x * nfWeightDeriv x) / nfWeight x ^ (2 : ℕ)
      = nfWeightSecondDeriv x := by
    have e2 : W * W - x ^ (2 : ℕ) = -1 := by
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
    (hode : (x ^ (2 : ℕ) - 1) * DDR x + 2 * x * DR x - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x = 0) :
    prolateNormalFormSolSecondDeriv R DR DDR x
      + radialProlateQ s c x * prolateNormalFormSol R x = 0 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hrsq : Real.sqrt (x ^ (2 : ℕ) - 1) * Real.sqrt (x ^ (2 : ℕ) - 1) = x ^ (2 : ℕ) - 1 :=
    Real.mul_self_sqrt hd.le
  obtain ⟨W, hW0, hWsq, hWeq⟩ : ∃ W : ℝ, 0 < W ∧ W * W = x ^ (2 : ℕ) - 1
      ∧ Real.sqrt (x ^ (2 : ℕ) - 1) = W := ⟨Real.sqrt (x ^ (2 : ℕ) - 1), hr, hrsq, rfl⟩
  have key : prolateNormalFormSolSecondDeriv R DR DDR x
      + radialProlateQ s c x * prolateNormalFormSol R x
      = ((x ^ (2 : ℕ) - 1) * DDR x + 2 * x * DR x - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x) / W := by
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
  lgAmplitude s x * (lgFirstOrderCoeff s x ^ (2 : ℕ) / 4 + lgFirstOrderCoeffDeriv s x / 2)

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
  have hval : (Du x * lgAmplitude s x - u x * lgAmplitudeDeriv s x) / lgAmplitude s x ^ (2 : ℕ)
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
        - (c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) + lgNormalFormDefect s c Q x) * comparisonSol u s x) x := by
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
    (hode : (x ^ (2 : ℕ) - 1) * DDR x + 2 * x * DR x - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x = 0) :
    HasDerivAt (comparisonSol (prolateNormalFormSol R) s)
        (comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x) x
      ∧ HasDerivAt (comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s)
        (-(lgFirstOrderCoeff s x)
            * comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x
          - (c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) + lgNormalFormDefect s c (radialProlateQ s c) x)
            * comparisonSol (prolateNormalFormSol R) s x) x
      ∧ |lgNormalFormDefect s c (radialProlateQ s c) x| ≤ 40 / (x ^ (2 : ℕ) - 1) := by
  have hu := hasDerivAt_prolateNormalFormSol hx hR
  have hDu := hasDerivAt_prolateNormalFormSolDeriv hx hR hDR
  have hnf := prolate_normalForm_ode (s := s) (c := c) hx hode
  exact ⟨hasDerivAt_comparisonSol hs0 hs1 hx hu,
    hasDerivAt_comparisonSolDeriv hs0 hs1 hx hu hDu hnf,
    abs_lgNormalFormDefect_radialProlate_le hs0 hs1 hx⟩



/-! ## The Liouville mass of the defect

The exponential factor of the Volterra estimate is the total mass of `m |a| E²`, and since
`m = xi/xi'` and `E² = C²/(c xi)` that mass is `(C²/c) int |a|/xi'`.  A simple pole has finite mass
against `dx/xi'` because `1/xi' = sqrt((x²-1)/(x²-s))` vanishes like `sqrt(x²-1)` at the endpoint; a
double pole would not.  Both blocks are exact: the endpoint block integrates `1/sqrt(x²-1)` and the far
block integrates `x^{-2}`. -/

/-- The integrand of the Liouville mass. -/
def defectMassIntegrand (s c t : ℝ) : ℝ :=
  |lgNormalFormDefect s c (radialProlateQ s c) t| / xiSpeed s t

theorem continuousOn_phaseLogDefect {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (phaseLogDefect s) (Set.Ioi 1) := by
  have hfun : phaseLogDefect s
      = fun t : ℝ => xiSpeed s t / xiEndpointPhase s t - t / (t ^ (2 : ℕ) - 1) := by
    funext t
    rw [phaseLogDefect]
  have h1 : ContinuousOn (fun t : ℝ => xiSpeed s t / xiEndpointPhase s t) (Set.Ioi 1) :=
    (continuousOn_xiSpeed s).div (continuousOn_xiEndpointPhase hs0)
      (fun t ht => (xiEndpointPhase_pos hs0 hs1 ht).ne')
  have h2 : ContinuousOn (fun t : ℝ => t / (t ^ (2 : ℕ) - 1)) (Set.Ioi 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
    exact this.ne'
  rw [hfun]
  exact h1.sub h2

theorem continuousOn_prolateDefectAlg {s : ℝ} (hs1 : s ≤ 1 / 2) :
    ContinuousOn (prolateDefectAlg s) (Set.Ioi 1) := by
  have hfun : prolateDefectAlg s
      = fun t : ℝ => (-(t ^ (4 : ℕ)) + (8 * s - 3) * t ^ (2 : ℕ) - 2 * s * (s + 1))
          / (4 * (t ^ (2 : ℕ) - s) ^ (2 : ℕ) * (t ^ (2 : ℕ) - 1)) := by
    funext t
    rw [prolateDefectAlg]
  rw [hfun]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro t ht
  have ht1 : (1 : ℝ) < t := ht
  have h1 : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have h2 : (0 : ℝ) < t ^ (2 : ℕ) - s := by nlinarith
  have : (0 : ℝ) < 4 * (t ^ (2 : ℕ) - s) ^ (2 : ℕ) * (t ^ (2 : ℕ) - 1) := by positivity
  exact this.ne'

theorem continuousOn_lgNormalFormDefect_radialProlate {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (fun t : ℝ => lgNormalFormDefect s c (radialProlateQ s c) t) (Set.Ioi 1) := by
  have hcont : ContinuousOn (fun t : ℝ => prolateDefectAlg s t
      - t * phaseLogDefect s t / (2 * (t ^ (2 : ℕ) - 1)) - phaseLogDefect s t ^ (2 : ℕ) / 4) (Set.Ioi 1) := by
    have hP := continuousOn_phaseLogDefect hs0 hs1
    have h2 : ContinuousOn (fun t : ℝ => t * phaseLogDefect s t / (2 * (t ^ (2 : ℕ) - 1)))
        (Set.Ioi 1) := by
      refine ContinuousOn.div ((by fun_prop : ContinuousOn (fun t : ℝ => t) (Set.Ioi 1)).mul hP)
        (by fun_prop) ?_
      intro t ht
      have ht1 : (1 : ℝ) < t := ht
      have h1 : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
      have : (0 : ℝ) < 2 * (t ^ (2 : ℕ) - 1) := by linarith
      exact this.ne'
    have h3 : ContinuousOn (fun t : ℝ => phaseLogDefect s t ^ (2 : ℕ) / 4) (Set.Ioi 1) :=
      (hP.pow 2).div_const 4
    exact ((continuousOn_prolateDefectAlg hs1).sub h2).sub h3
  refine hcont.congr ?_
  intro t ht
  exact lgNormalFormDefect_radialProlate_eq_alg hs0 hs1 ht

theorem continuousOn_defectMassIntegrand {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (defectMassIntegrand s c) (Set.Ioi 1) := by
  have hfun : defectMassIntegrand s c
      = fun t : ℝ => |lgNormalFormDefect s c (radialProlateQ s c) t| / xiSpeed s t := by
    funext t
    rw [defectMassIntegrand]
  rw [hfun]
  refine ContinuousOn.div ?_ (continuousOn_xiSpeed s) (fun t ht => (xiSpeed_pos hs1 ht).ne')
  exact (continuousOn_lgNormalFormDefect_radialProlate hs0 hs1).abs

/-- Near the endpoint the mass integrand is at most `40 sqrt 2 / sqrt(x²-1)`: the simple pole of the
defect meets the vanishing Liouville measure `1/xi' <= sqrt 2 sqrt(x²-1)`. -/
theorem defectMassIntegrand_le_near {s c t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ht : 1 < t) :
    defectMassIntegrand s c t ≤ 40 * Real.sqrt 2 * (1 / Real.sqrt (t ^ (2 : ℕ) - 1)) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hd : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < t ^ (2 : ℕ) - s := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (t ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
  have hV : 0 < xiSpeed s t := xiSpeed_pos hs1 ht
  have ha := abs_lgNormalFormDefect_radialProlate_le (s := s) (c := c) hs0 hs1 ht
  -- `1/xi' <= sqrt 2 sqrt(t²-1)`
  have hinv : 1 / xiSpeed s t ≤ Real.sqrt 2 * Real.sqrt (t ^ (2 : ℕ) - 1) := by
    have hsq : (Real.sqrt 2 * Real.sqrt (t ^ (2 : ℕ) - 1)) * xiSpeed s t
        = Real.sqrt (2 * (t ^ (2 : ℕ) - 1) * ((t ^ (2 : ℕ) - s) / (t ^ (2 : ℕ) - 1))) := by
      rw [xiSpeed, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.sqrt_mul (by positivity)]
    have hge : (1 : ℝ) ≤ Real.sqrt (2 * (t ^ (2 : ℕ) - 1) * ((t ^ (2 : ℕ) - s) / (t ^ (2 : ℕ) - 1))) := by
      rw [show 2 * (t ^ (2 : ℕ) - 1) * ((t ^ (2 : ℕ) - s) / (t ^ (2 : ℕ) - 1)) = 2 * (t ^ (2 : ℕ) - s) by field_simp]
      have : (1 : ℝ) ≤ 2 * (t ^ (2 : ℕ) - s) := by nlinarith
      calc (1 : ℝ) = Real.sqrt 1 := by rw [Real.sqrt_one]
        _ ≤ _ := Real.sqrt_le_sqrt this
    rw [div_le_iff₀ hV]
    linarith [hsq.le, hsq.ge, hge]
  calc defectMassIntegrand s c t
      = |lgNormalFormDefect s c (radialProlateQ s c) t| * (1 / xiSpeed s t) := by
        rw [defectMassIntegrand]
        ring
    _ ≤ (40 / (t ^ (2 : ℕ) - 1)) * (Real.sqrt 2 * Real.sqrt (t ^ (2 : ℕ) - 1)) := by
        apply mul_le_mul ha hinv (by positivity) (by positivity)
    _ = 40 * Real.sqrt 2 * (1 / Real.sqrt (t ^ (2 : ℕ) - 1)) := by
        obtain ⟨R, hR0, hRsq, hReq⟩ : ∃ R : ℝ, 0 < R ∧ R * R = t ^ (2 : ℕ) - 1
            ∧ Real.sqrt (t ^ (2 : ℕ) - 1) = R := ⟨Real.sqrt (t ^ (2 : ℕ) - 1), hr, Real.mul_self_sqrt hd.le, rfl⟩
        rw [hReq, ← hRsq]
        field_simp

/-- Away from the endpoint the mass integrand is at most `(160/3) x^{-2}`, because `xi' >= 1` there and
`1/(x²-1) <= (4/3)/x²` for `x >= 2`. -/
theorem defectMassIntegrand_le_far {s c t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ht : 2 ≤ t) :
    defectMassIntegrand s c t ≤ 160 / 3 * (1 / t ^ (2 : ℕ)) := by
  have ht1 : (1 : ℝ) < t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hd : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have hV : 1 ≤ xiSpeed s t := one_le_xiSpeed (by linarith) ht1
  have ha := abs_lgNormalFormDefect_radialProlate_le (s := s) (c := c) hs0 hs1 ht1
  have habs : (0 : ℝ) ≤ |lgNormalFormDefect s c (radialProlateQ s c) t| := abs_nonneg _
  have hstep : defectMassIntegrand s c t ≤ |lgNormalFormDefect s c (radialProlateQ s c) t| := by
    rw [defectMassIntegrand, div_le_iff₀ (lt_of_lt_of_le zero_lt_one hV)]
    nlinarith
  have hfar : (40 : ℝ) / (t ^ (2 : ℕ) - 1) ≤ 160 / 3 * (1 / t ^ (2 : ℕ)) := by
    rw [div_le_iff₀ hd]
    rw [show (160 : ℝ) / 3 * (1 / t ^ (2 : ℕ)) = 160 / (3 * t ^ (2 : ℕ)) by ring,
      div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  linarith [hstep, ha, hfar]



theorem intervalIntegrable_defectMassIntegrand {s c A B : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hA : 1 < A) (hAB : A ≤ B) :
    IntervalIntegrable (defectMassIntegrand s c) MeasureTheory.volume A B := by
  have hsub : Set.uIcc A B ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hAB]
    intro t ht
    exact lt_of_lt_of_le hA ht.1
  exact ((continuousOn_defectMassIntegrand hs0 hs1).mono hsub).intervalIntegrable

/-- **The endpoint block of the Liouville mass.**  On any interval inside `(1, 2]` the mass is at most
`100`, from the exact primitive `int 1/sqrt(t²-1) = log(t + sqrt(t²-1))` and `log(2 + sqrt 3) <= sqrt 3`. -/
theorem integral_defectMassIntegrand_near_le {s c A B : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hA : 1 < A) (hAB : A ≤ B) (hB : B ≤ 2) :
    (∫ t in A..B, defectMassIntegrand s c t) ≤ 100 := by
  have hsub : Set.uIcc A B ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hAB]
    intro t ht
    exact lt_of_lt_of_le hA ht.1
  have hmaj : ContinuousOn
      (fun t : ℝ => 40 * Real.sqrt 2 * (1 / Real.sqrt (t ^ (2 : ℕ) - 1))) (Set.Ioi 1) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact Real.continuous_sqrt.comp_continuousOn (by fun_prop)
    · intro t ht
      have ht1 : (1 : ℝ) < t := ht
      have hd : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
      exact (Real.sqrt_pos.mpr hd).ne'
  have hgint : IntervalIntegrable (fun t : ℝ => 40 * Real.sqrt 2 * (1 / Real.sqrt (t ^ (2 : ℕ) - 1)))
      MeasureTheory.volume A B := (hmaj.mono hsub).intervalIntegrable
  have hmono : (∫ t in A..B, defectMassIntegrand s c t)
      ≤ ∫ t in A..B, 40 * Real.sqrt 2 * (1 / Real.sqrt (t ^ (2 : ℕ) - 1)) := by
    refine intervalIntegral.integral_mono_on hAB
      (intervalIntegrable_defectMassIntegrand hs0 hs1 hA hAB) hgint ?_
    intro t ht
    exact defectMassIntegrand_le_near hs0 hs1 (lt_of_lt_of_le hA ht.1)
  have hFTC : (∫ t in A..B, 40 * Real.sqrt 2 * (1 / Real.sqrt (t ^ (2 : ℕ) - 1)))
      = 40 * Real.sqrt 2 * GaloisForLFunctions.HTGeometry.endpointLog B
        - 40 * Real.sqrt 2 * GaloisForLFunctions.HTGeometry.endpointLog A := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ =>
      40 * Real.sqrt 2 * GaloisForLFunctions.HTGeometry.endpointLog t) ?_ hgint
    intro t ht
    have ht1 : (1 : ℝ) < t := hsub ht
    exact (GaloisForLFunctions.HTGeometry.hasDerivAt_endpointLog ht1).const_mul _
  have hLB : GaloisForLFunctions.HTGeometry.endpointLog B ≤ Real.sqrt 3 := by
    refine le_trans (GaloisForLFunctions.HTGeometry.endpointLog_le_sqrt (by linarith)) ?_
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hLA : 0 ≤ GaloisForLFunctions.HTGeometry.endpointLog A := by
    have h := GaloisForLFunctions.HTGeometry.sqrt_mul_one_sub_le_endpointLog (x := A) (by linarith)
    have hd : (0 : ℝ) < A ^ (2 : ℕ) - 1 := by nlinarith
    have hd3 : A ^ (2 : ℕ) - 1 ≤ 3 := by nlinarith
    have hr : 0 < Real.sqrt (A ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd
    nlinarith [h, hr]
  have h6 : Real.sqrt 2 * Real.sqrt 3 ≤ 5 / 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (5 : ℝ) / 2 = Real.sqrt ((5 / 2) ^ (2 : ℕ)) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hfin : 40 * Real.sqrt 2 * GaloisForLFunctions.HTGeometry.endpointLog B
      - 40 * Real.sqrt 2 * GaloisForLFunctions.HTGeometry.endpointLog A ≤ 100 := by
    have h1 : 40 * Real.sqrt 2 * GaloisForLFunctions.HTGeometry.endpointLog B
        ≤ 40 * (Real.sqrt 2 * Real.sqrt 3) := by
      have := mul_le_mul_of_nonneg_left hLB (by positivity : (0 : ℝ) ≤ 40 * Real.sqrt 2)
      nlinarith [this]
    have h3 : 0 ≤ 40 * Real.sqrt 2 * GaloisForLFunctions.HTGeometry.endpointLog A := by
      positivity
    nlinarith [h1, h3, h6]
  linarith [hmono, hFTC.le, hFTC.ge, hfin]

/-- **The far block of the Liouville mass.**  Beyond `x = 2` the speed is at least `1` and the pole is
harmless: the mass is at most `27`, from `int_A^B x^{-2} = 1/A - 1/B <= 1/2`. -/
theorem integral_defectMassIntegrand_far_le {s c A B : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hA : 2 ≤ A) (hAB : A ≤ B) :
    (∫ t in A..B, defectMassIntegrand s c t) ≤ 27 := by
  have hA1 : (1 : ℝ) < A := by linarith
  have hsub : Set.uIcc A B ⊆ Set.Ici 2 := by
    rw [Set.uIcc_of_le hAB]
    intro t ht
    exact le_trans hA ht.1
  have hmaj : ContinuousOn (fun t : ℝ => 160 / 3 * (1 / t ^ (2 : ℕ))) (Set.Ici 2) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    have : (0 : ℝ) < t ^ (2 : ℕ) := by nlinarith
    exact this.ne'
  have hgint : IntervalIntegrable (fun t : ℝ => 160 / 3 * (1 / t ^ (2 : ℕ)))
      MeasureTheory.volume A B := (hmaj.mono hsub).intervalIntegrable
  have hmono : (∫ t in A..B, defectMassIntegrand s c t)
      ≤ ∫ t in A..B, 160 / 3 * (1 / t ^ (2 : ℕ)) := by
    refine intervalIntegral.integral_mono_on hAB
      (intervalIntegrable_defectMassIntegrand hs0 hs1 hA1 hAB) hgint ?_
    intro t ht
    exact defectMassIntegrand_le_far hs0 hs1 (le_trans hA ht.1)
  have hFTC : (∫ t in A..B, 160 / 3 * (1 / t ^ (2 : ℕ))) = -(160 / 3 * (1 / B)) - -(160 / 3 * (1 / A)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => -(160 / 3 * (1 / t))) ?_ hgint
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := hsub ht
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht2
      norm_num at ht2
    have h := ((hasDerivAt_inv ht0).const_mul (160 / 3 : ℝ)).neg
    have hval : -(160 / 3 * -(t ^ (2 : ℕ))⁻¹) = 160 / 3 * (1 / t ^ (2 : ℕ)) := by
      field_simp
    rw [← hval]
    have hfun : (fun t : ℝ => -(160 / 3 * (1 / t))) = fun t : ℝ => -(160 / 3 * t⁻¹) := by
      funext u
      rw [one_div]
    rw [hfun]
    exact h
  have hB0 : (0 : ℝ) < B := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hinvA : 1 / A ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hA
  have hinvB : 0 ≤ 1 / B := by positivity
  have hfin : -(160 / 3 * (1 / B)) - -(160 / 3 * (1 / A)) ≤ 27 := by
    nlinarith [hinvA, hinvB]
  linarith [hmono, hFTC.le, hFTC.ge, hfin]

/-- **The Liouville mass of the defect is bounded, uniformly in every parameter.**  For every
`1 < A <= B`,

```text
int_A^B |a|/xi' <= 127.
```

Since the transport-law integrand of the Volterra estimate is
`2 m |a| (C/sqrt(c xi))² / W = (2C²/(cW)) |a|/xi'`, this makes the exponential factor of the pole-uniform
estimate `exp(O(1/c))`, i.e. a relative error `1 + O(c^{-1})` — the `O(c^{-1})` of Dunster's expansion
`(14)`.  The endpoint block is where the simple pole meets the vanishing Liouville measure; the far block
is where the pole decays like `x^{-2}`. -/
theorem integral_defectMassIntegrand_le {s c A B : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hA : 1 < A) (hAB : A ≤ B) :
    (∫ t in A..B, defectMassIntegrand s c t) ≤ 127 := by
  rcases le_or_gt B 2 with hB | hB
  · linarith [integral_defectMassIntegrand_near_le (s := s) (c := c) hs0 hs1 hA hAB hB]
  rcases le_or_gt 2 A with hA2 | hA2
  · linarith [integral_defectMassIntegrand_far_le (s := s) (c := c) hs0 hs1 hA2 hAB]
  · have h1 := intervalIntegrable_defectMassIntegrand (s := s) (c := c) hs0 hs1 hA hA2.le
    have h2 := intervalIntegrable_defectMassIntegrand (s := s) (c := c) hs0 hs1
      (by norm_num : (1 : ℝ) < 2) hB.le
    have hsplit : (∫ t in A..(2 : ℝ), defectMassIntegrand s c t)
        + (∫ t in (2 : ℝ)..B, defectMassIntegrand s c t)
        = ∫ t in A..B, defectMassIntegrand s c t :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hnear := integral_defectMassIntegrand_near_le (s := s) (c := c) hs0 hs1 hA hA2.le
      (le_refl 2)
    have hfar := integral_defectMassIntegrand_far_le (s := s) (c := c) hs0 hs1 (le_refl 2) hB.le
    linarith [hsplit, hnear, hfar]



/-- **The exponential factor of the pole-uniform estimate is `exp(O(1/c))`.**  The Volterra exponent of
`abs_perturbed_le_lgEnvelope_mul_exp` is the mass of `2 m |a| E² / W`, and with `m = xi/xi'` and
`E = C/sqrt(c xi)` that integrand is exactly `(2C²/(cW)) |a|/xi'`.  So the whole exponent is at most
`254 C²/(c W)` — the relative error of the pole-uniform expansion `(14)` is `1 + O(c^{-1})`. -/
theorem integral_volterra_exponent_le {s c A B C W : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hW : 0 < W) (hA : 1 < A) (hAB : A ≤ B) :
    (∫ t in A..B, 2 * (lgWeight s t * |lgNormalFormDefect s c (radialProlateQ s c) t|)
        * (C / Real.sqrt (c * xiEndpointPhase s t)) ^ (2 : ℕ) / W)
      ≤ 2 * C ^ (2 : ℕ) / (c * W) * 127 := by
  have hsub : Set.uIcc A B ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hAB]
    intro t ht
    exact lt_of_lt_of_le hA ht.1
  have heq : Set.EqOn (fun t : ℝ => 2 * (lgWeight s t * |lgNormalFormDefect s c (radialProlateQ s c) t|)
        * (C / Real.sqrt (c * xiEndpointPhase s t)) ^ (2 : ℕ) / W)
      (fun t : ℝ => 2 * C ^ (2 : ℕ) / (c * W) * defectMassIntegrand s c t) (Set.uIcc A B) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := hsub ht
    have hxi : 0 < xiEndpointPhase s t := xiEndpointPhase_pos hs0 hs1 ht1
    have hV : 0 < xiSpeed s t := xiSpeed_pos hs1 ht1
    have hsq : Real.sqrt (c * xiEndpointPhase s t) ^ (2 : ℕ) = c * xiEndpointPhase s t :=
      Real.sq_sqrt (by positivity)
    simp only [defectMassIntegrand, lgWeight, div_pow, hsq]
    field_simp
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_defectMassIntegrand_le (s := s) (c := c) hs0 hs1 hA hAB)
    (by positivity)



/-! ## Equation (14) for the actual radial mode -/

/-- **Dunster's pole-uniform bound `(14)` for the actual radial prolate mode.**  Let `R` solve the radial
spheroidal equation of order zero with separation constant `chi = s c²`, `0 <= s <= 1/2`, on an interval
`[A, B]` inside `(1, ∞)` on which the Bessel argument has already reached one, `c xi_s(A) >= 1`.  Then the
Liouville–Green transform `U = sqrt(x²-1) R / sqrt(xi/xi')` obeys the Bessel envelope

```text
|U x| <= (C / sqrt(c xi_s(x))) / W · S(A) · exp(254 C²/(c W)),
```

with `W` the Green kernel constant and `S(A)` the total weighted Wronskian size at the left endpoint.  The
exponential is `1 + O(c^{-1})`: that factor is the relative error of the pole-uniform expansion, and it is
now unconditional.  Every ingredient is a theorem of this tree — the two model ODEs, their common envelope,
the positive constant Green kernel normalisation, the two transport laws, the algebraic reconstruction, the
variable-coefficient Grönwall inequality, the exact defect identity, its simple pole and its finite
Liouville mass. -/
theorem abs_radialProlate_comparison_le {s c A B : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hA : 1 < A) (hAB : A ≤ B)
    (hcxi : 1 ≤ c * xiEndpointPhase s A)
    (hR : ∀ x ∈ Set.Icc A B, HasDerivAt R (DR x) x)
    (hDR : ∀ x ∈ Set.Icc A B, HasDerivAt DR (DDR x) x)
    (hode : ∀ x ∈ Set.Icc A B,
      (x ^ (2 : ℕ) - 1) * DDR x + 2 * x * DR x - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc A B,
      |comparisonSol (prolateNormalFormSol R) s x|
        ≤ C / Real.sqrt (c * xiEndpointPhase s x)
            / besselWronskian (c * xiEndpointPhase s A)
          * ((|lgWeight s A * (comparisonSol (prolateNormalFormSol R) s A
                  * lgBesselModelDeriv s c A
                - comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s A
                  * lgBesselModel s c A)|
              + |lgWeight s A * (comparisonSol (prolateNormalFormSol R) s A
                  * lgBesselModel2Deriv s c A
                - comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s A
                  * lgBesselModel2 s c A)|)
            * Real.exp (2 * C ^ (2 : ℕ)
                / (c * besselWronskian (c * xiEndpointPhase s A)) * 127)) := by
  obtain ⟨C, hC0, hC⟩ := exists_lgBesselModel_common_envelope
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hsub : Set.Icc A B ⊆ Set.Ioi 1 := fun t ht => lt_of_lt_of_le hA ht.1
  have hW : 0 < besselWronskian (c * xiEndpointPhase s A) :=
    besselWronskian_phase_pos hs0 hs1 hc hA
  have hU : ∀ t ∈ Set.Icc A B, HasDerivAt (comparisonSol (prolateNormalFormSol R) s)
      (comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s t) t :=
    fun t ht => (radialProlate_comparison_pole_uniform hs0 hs1 (hsub ht) (hR t ht) (hDR t ht)
      (hode t ht)).1
  have hDU : ∀ t ∈ Set.Icc A B,
      HasDerivAt (comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s)
        (-(lgFirstOrderCoeff s t)
            * comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s t
          - (c ^ (2 : ℕ) * xiSpeed s t ^ (2 : ℕ) + lgNormalFormDefect s c (radialProlateQ s c) t)
            * comparisonSol (prolateNormalFormSol R) s t) t :=
    fun t ht => (radialProlate_comparison_pole_uniform hs0 hs1 (hsub ht) (hR t ht) (hDR t ht)
      (hode t ht)).2.1
  have hac : ContinuousOn (fun t : ℝ => lgNormalFormDefect s c (radialProlateQ s c) t)
      (Set.Icc A B) := (continuousOn_lgNormalFormDefect_radialProlate hs0 hs1).mono hsub
  have hmain := abs_perturbed_le_lgEnvelope_mul_exp
    (a := fun t : ℝ => lgNormalFormDefect s c (radialProlateQ s c) t)
    hs0 hs1 hc hA hAB hC0 hcxi (fun y hy => hC s c y hy) hac hU hDU x hx
  have hexp : (∫ t in A..x, 2 * (lgWeight s t * |lgNormalFormDefect s c (radialProlateQ s c) t|)
        * (C / Real.sqrt (c * xiEndpointPhase s t)) ^ (2 : ℕ)
        / besselWronskian (c * xiEndpointPhase s A))
      ≤ 2 * C ^ (2 : ℕ) / (c * besselWronskian (c * xiEndpointPhase s A)) * 127 :=
    integral_volterra_exponent_le hs0 hs1 hc hW hA hx.1
  have hxpos : 0 < Real.sqrt (c * xiEndpointPhase s x) :=
    Real.sqrt_pos.mpr (mul_pos hc (xiEndpointPhase_pos hs0 hs1 (hsub hx)))
  have hE : 0 ≤ C / Real.sqrt (c * xiEndpointPhase s x)
      / besselWronskian (c * xiEndpointPhase s A) :=
    div_nonneg (div_nonneg hC0 hxpos.le) hW.le
  have hS : (0 : ℝ) ≤ |lgWeight s A * (comparisonSol (prolateNormalFormSol R) s A
        * lgBesselModelDeriv s c A
      - comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s A
        * lgBesselModel s c A)|
    + |lgWeight s A * (comparisonSol (prolateNormalFormSol R) s A * lgBesselModel2Deriv s c A
      - comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s A
        * lgBesselModel2 s c A)| := by positivity
  refine hmain.trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hS) hE



/-! ## The approximation form of (14)

The envelope bound says the transform is *at most* the Bessel envelope.  What the Gram estimate needs is
sharper: that it *is* a fixed combination of the two model solutions, up to `O(c^{-1})` times the envelope.
That follows from the same three ingredients — the algebraic reconstruction, the two transport laws, and the
finite defect mass — with no further analysis: the reconstruction is exact, and the transport laws move the
two Wronskians by exactly the defect integral. -/

private theorem abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa [abs_neg] using abs_add_le a (-b)

/-- **A perturbed solution is a fixed combination of the two model solutions, up to the defect mass.**
If `U` solves the comparison equation with defect `a` on `[A, B]`, both model solutions are bounded by an
envelope `E` there, `|U| <= E K`, and the defect has Liouville mass at most `M`, then

```text
|U(x) W - (F_2(A) V_1(x) - F_1(A) V_2(x))| <= 2 K M E(x),
```

where `F_i` are the weighted Wronskians of `U` against the model pair.  The proof is exact: the
reconstruction identity gives `U W = F_2 V_1 - F_1 V_2` pointwise, and each `F_i` differs from its value at
`A` by exactly `int m a U V_i`. -/
theorem abs_perturbed_sub_model_le {s c A B K M : ℝ} {U DU a E : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hA : 1 < A) (_hAB : A ≤ B) (hK : 0 ≤ K)
    (hM : 0 ≤ M)
    (hU : ∀ x ∈ Set.Icc A B, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Set.Icc A B, HasDerivAt DU (-(lgFirstOrderCoeff s x) * DU x
      - (c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) + a x) * U x) x)
    (hEnv : ∀ x ∈ Set.Icc A B, |lgBesselModel s c x| ≤ E x ∧ |lgBesselModel2 s c x| ≤ E x)
    (hUb : ∀ x ∈ Set.Icc A B, |U x| ≤ E x * K)
    (hi1 : ∀ x ∈ Set.Icc A B, IntervalIntegrable
      (fun t : ℝ => lgWeight s t * a t * (U t * lgBesselModel s c t)) MeasureTheory.volume A x)
    (hi2 : ∀ x ∈ Set.Icc A B, IntervalIntegrable
      (fun t : ℝ => lgWeight s t * a t * (U t * lgBesselModel2 s c t)) MeasureTheory.volume A x)
    (hmi : ∀ x ∈ Set.Icc A B, IntervalIntegrable
      (fun t : ℝ => lgWeight s t * |a t| * E t ^ (2 : ℕ)) MeasureTheory.volume A x)
    (hmass : ∀ x ∈ Set.Icc A B, (∫ t in A..x, lgWeight s t * |a t| * E t ^ (2 : ℕ)) ≤ M) :
    ∀ x ∈ Set.Icc A B,
      |U x * besselWronskian (c * xiEndpointPhase s A)
          - ((lgWeight s A * (U A * lgBesselModel2Deriv s c A - DU A * lgBesselModel2 s c A))
              * lgBesselModel s c x
            - (lgWeight s A * (U A * lgBesselModelDeriv s c A - DU A * lgBesselModel s c A))
              * lgBesselModel2 s c x)|
        ≤ 2 * (K * M) * E x := by
  intro x hx
  have hAx : A ≤ x := hx.1
  have hxsub : Set.uIcc A x ⊆ Set.Icc A B := by
    rw [Set.uIcc_of_le hAx]
    exact fun t ht => ⟨ht.1, le_trans ht.2 hx.2⟩
  have hU' : ∀ t ∈ Set.uIcc A x, HasDerivAt U (DU t) t := fun t ht => hU t (hxsub ht)
  have hDU' : ∀ t ∈ Set.uIcc A x, HasDerivAt DU (-(lgFirstOrderCoeff s t) * DU t
      - (c ^ (2 : ℕ) * xiSpeed s t ^ (2 : ℕ) + a t) * U t) t := fun t ht => hDU t (hxsub ht)
  have hrec := lgReconstruction_const (U := U) (DU := DU) hs0 hs1 hc hA hAx
  have htr1 := integral_lgBesselWronskian hs0 hs1 hc hAx hA hU' hDU' (hi1 x hx)
  have htr2 := integral_lgBessel2Wronskian hs0 hs1 hc hAx hA hU' hDU' (hi2 x hx)
  have hEx : 0 ≤ E x := le_trans (abs_nonneg _) (hEnv x hx).1
  have hbound : ∀ V : ℝ → ℝ, (∀ t ∈ Set.Icc A B, |V t| ≤ E t) →
      IntervalIntegrable (fun t : ℝ => lgWeight s t * a t * (U t * V t)) MeasureTheory.volume A x →
      |∫ t in A..x, lgWeight s t * a t * (U t * V t)| ≤ K * M := by
    intro V hV hint
    have h1 : |∫ t in A..x, lgWeight s t * a t * (U t * V t)|
        ≤ ∫ t in A..x, |lgWeight s t * a t * (U t * V t)| := by
      have h := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
        (f := fun t : ℝ => lgWeight s t * a t * (U t * V t)) hAx
      simpa [Real.norm_eq_abs] using h
    have h2 : (∫ t in A..x, |lgWeight s t * a t * (U t * V t)|)
        ≤ ∫ t in A..x, K * (lgWeight s t * |a t| * E t ^ (2 : ℕ)) := by
      refine intervalIntegral.integral_mono_on hAx hint.abs ((hmi x hx).const_mul K) ?_
      intro t ht
      have htIcc : t ∈ Set.Icc A B := hxsub (by rw [Set.uIcc_of_le hAx]; exact ht)
      have hm : 0 < lgWeight s t := lgWeight_pos hs0 hs1 (lt_of_lt_of_le hA htIcc.1)
      have hEt : 0 ≤ E t := le_trans (abs_nonneg _) (hEnv t htIcc).1
      calc |lgWeight s t * a t * (U t * V t)|
          = lgWeight s t * |a t| * (|U t| * |V t|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hm]
        _ ≤ lgWeight s t * |a t| * ((E t * K) * E t) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hm.le (abs_nonneg _))
            exact mul_le_mul (hUb t htIcc) (hV t htIcc) (abs_nonneg _) (by positivity)
        _ = K * (lgWeight s t * |a t| * E t ^ (2 : ℕ)) := by ring
    have h3 : (∫ t in A..x, K * (lgWeight s t * |a t| * E t ^ (2 : ℕ)))
        = K * ∫ t in A..x, lgWeight s t * |a t| * E t ^ (2 : ℕ) :=
      intervalIntegral.integral_const_mul _ _
    have h4 : K * (∫ t in A..x, lgWeight s t * |a t| * E t ^ (2 : ℕ)) ≤ K * M :=
      mul_le_mul_of_nonneg_left (hmass x hx) hK
    linarith [h1, h2, h3.le, h3.ge, h4]
  have hb1 := hbound (lgBesselModel s c) (fun t ht => (hEnv t ht).1) (hi1 x hx)
  have hb2 := hbound (lgBesselModel2 s c) (fun t ht => (hEnv t ht).2) (hi2 x hx)
  have hid : U x * besselWronskian (c * xiEndpointPhase s A)
      - ((lgWeight s A * (U A * lgBesselModel2Deriv s c A - DU A * lgBesselModel2 s c A))
          * lgBesselModel s c x
        - (lgWeight s A * (U A * lgBesselModelDeriv s c A - DU A * lgBesselModel s c A))
          * lgBesselModel2 s c x)
      = (∫ t in A..x, lgWeight s t * a t * (U t * lgBesselModel2 s c t)) * lgBesselModel s c x
        - (∫ t in A..x, lgWeight s t * a t * (U t * lgBesselModel s c t))
          * lgBesselModel2 s c x := by
    linear_combination hrec - lgBesselModel s c x * htr2 + lgBesselModel2 s c x * htr1
  rw [hid]
  refine le_trans (abs_sub_le' _ _) ?_
  have h1 : |(∫ t in A..x, lgWeight s t * a t * (U t * lgBesselModel2 s c t))
      * lgBesselModel s c x| ≤ K * M * E x := by
    rw [abs_mul]
    exact mul_le_mul hb2 (hEnv x hx).1 (abs_nonneg _) (mul_nonneg hK hM)
  have h2 : |(∫ t in A..x, lgWeight s t * a t * (U t * lgBesselModel s c t))
      * lgBesselModel2 s c x| ≤ K * M * E x := by
    rw [abs_mul]
    exact mul_le_mul hb1 (hEnv x hx).2 (abs_nonneg _) (mul_nonneg hK hM)
  linarith [h1, h2]



/-! ## The mass of the defect against the model envelope -/

theorem intervalIntegrable_lgWeight_abs_defect_envelope {s c C A B : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hA : 1 < A) (hAB : A ≤ B) :
    IntervalIntegrable (fun t : ℝ => lgWeight s t
        * |lgNormalFormDefect s c (radialProlateQ s c) t|
        * (C / Real.sqrt (c * xiEndpointPhase s t)) ^ (2 : ℕ)) MeasureTheory.volume A B := by
  have hsub : Set.uIcc A B ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hAB]
    exact fun t ht => lt_of_lt_of_le hA ht.1
  have hsqrt : ContinuousOn (fun t : ℝ => Real.sqrt (c * xiEndpointPhase s t)) (Set.uIcc A B) :=
    Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.mul ((continuousOn_xiEndpointPhase hs0).mono hsub))
  have hpow : ContinuousOn (fun t : ℝ => (C / Real.sqrt (c * xiEndpointPhase s t)) ^ (2 : ℕ))
      (Set.uIcc A B) := by
    refine ContinuousOn.pow (ContinuousOn.div continuousOn_const hsqrt ?_) 2
    intro t ht
    exact (Real.sqrt_pos.mpr (mul_pos hc (xiEndpointPhase_pos hs0 hs1 (hsub ht)))).ne'
  refine (ContinuousOn.mul (ContinuousOn.mul ((continuousOn_lgWeight hs0 hs1).mono hsub)
    (((continuousOn_lgNormalFormDefect_radialProlate hs0 hs1).mono hsub).abs)) hpow).intervalIntegrable

/-- **The defect mass against the model envelope is `O(1/c)`.**  Pointwise
`m |a| E² = (C²/c) |a|/xi'`, because the Liouville weight `m = xi/xi'` cancels the envelope's `1/xi`; the
mass bound then gives `127 C²/c`. -/
theorem integral_lgWeight_abs_defect_envelope_le {s c C A B : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hA : 1 < A) (hAB : A ≤ B) :
    (∫ t in A..B, lgWeight s t * |lgNormalFormDefect s c (radialProlateQ s c) t|
        * (C / Real.sqrt (c * xiEndpointPhase s t)) ^ (2 : ℕ)) ≤ 127 * C ^ (2 : ℕ) / c := by
  have hsub : Set.uIcc A B ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hAB]
    exact fun t ht => lt_of_lt_of_le hA ht.1
  have heq : Set.EqOn (fun t : ℝ => lgWeight s t
        * |lgNormalFormDefect s c (radialProlateQ s c) t|
        * (C / Real.sqrt (c * xiEndpointPhase s t)) ^ (2 : ℕ))
      (fun t : ℝ => C ^ (2 : ℕ) / c * defectMassIntegrand s c t) (Set.uIcc A B) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := hsub ht
    have hxi : 0 < xiEndpointPhase s t := xiEndpointPhase_pos hs0 hs1 ht1
    have hV : 0 < xiSpeed s t := xiSpeed_pos hs1 ht1
    have hsq : Real.sqrt (c * xiEndpointPhase s t) ^ (2 : ℕ) = c * xiEndpointPhase s t :=
      Real.sq_sqrt (by positivity)
    simp only [defectMassIntegrand, lgWeight, div_pow, hsq]
    field_simp
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul]
  calc C ^ (2 : ℕ) / c * ∫ t in A..B, defectMassIntegrand s c t
      ≤ C ^ (2 : ℕ) / c * 127 :=
        mul_le_mul_of_nonneg_left (integral_defectMassIntegrand_le (s := s) (c := c) hs0 hs1 hA hAB)
          (by positivity)
    _ = 127 * C ^ (2 : ℕ) / c := by ring

/-! ## Equation (14) in approximation form for the actual radial mode -/

/-- Total weighted Wronskian datum at the left endpoint of the interior Dunster interval. -/
def radialProlateVolterraDatum (s c A : ℝ) (R DR : ℝ → ℝ) : ℝ :=
  |lgWeight s A * (comparisonSol (prolateNormalFormSol R) s A * lgBesselModelDeriv s c A
      - comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s A
        * lgBesselModel s c A)|
    + |lgWeight s A *
      (comparisonSol (prolateNormalFormSol R) s A * lgBesselModel2Deriv s c A
        - comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s A
          * lgBesselModel2 s c A)|

/-- Explicit Grönwall constant used in the actual radial Dunster approximation. -/
def radialProlateVolterraK (s c A : ℝ) (R DR : ℝ → ℝ) (C : ℝ) : ℝ :=
  radialProlateVolterraDatum s c A R DR *
      Real.exp (2 * C ^ (2 : ℕ) / (c * besselWronskian (c * xiEndpointPhase s A)) * 127) /
    besselWronskian (c * xiEndpointPhase s A)

/-- **Dunster's expansion `(14)` for the actual radial prolate mode, in approximation form.**  Under the
hypotheses of the envelope bound, the Liouville–Green transform of the radial mode is a *fixed* linear
combination of the two Bessel model solutions, up to `O(c^{-1})` times the common envelope:

```text
|U(x) W - (F_2(A) J_0(c xi) - F_1(A) K(c xi))| <= 2 K_0 (127 C²/c) · C/sqrt(c xi_s(x)),
```

with `K_0` the endpoint Wronskian datum divided by `W` and dressed by the Volterra exponential.  This is the
form the Gram estimate `(17)` consumes: the leading term is the model, and the remainder carries one factor
`c^{-1}` against the same envelope. -/
theorem abs_radialProlate_sub_model_le {s c A B : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hA : 1 < A) (hAB : A ≤ B)
    (hcxi : 1 ≤ c * xiEndpointPhase s A)
    (hR : ∀ x ∈ Set.Icc A B, HasDerivAt R (DR x) x)
    (hDR : ∀ x ∈ Set.Icc A B, HasDerivAt DR (DDR x) x)
    (hode : ∀ x ∈ Set.Icc A B,
      (x ^ (2 : ℕ) - 1) * DDR x + 2 * x * DR x - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x = 0) :
    ∃ C K : ℝ, 0 ≤ C ∧ C = lgBesselCommonEnvelopeConstant ∧ 0 ≤ K ∧
      (∀ s' c' x' : ℝ, 1 ≤ c' * xiEndpointPhase s' x' →
        |lgBesselModel s' c' x'| ≤ C / Real.sqrt (c' * xiEndpointPhase s' x') ∧
        |lgBesselModel2 s' c' x'| ≤ C / Real.sqrt (c' * xiEndpointPhase s' x')) ∧
      K = radialProlateVolterraK s c A R DR C ∧
      ∀ x ∈ Set.Icc A B,
      |comparisonSol (prolateNormalFormSol R) s x * besselWronskian (c * xiEndpointPhase s A)
          - ((lgWeight s A * (comparisonSol (prolateNormalFormSol R) s A
                  * lgBesselModel2Deriv s c A
                - comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s A
                  * lgBesselModel2 s c A)) * lgBesselModel s c x
            - (lgWeight s A * (comparisonSol (prolateNormalFormSol R) s A
                  * lgBesselModelDeriv s c A
                - comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s A
                  * lgBesselModel s c A)) * lgBesselModel2 s c x)|
        ≤ 2 * (K * (127 * C ^ (2 : ℕ) / c)) * (C / Real.sqrt (c * xiEndpointPhase s x)) := by
  let C : ℝ := lgBesselCommonEnvelopeConstant
  have hC0 : 0 ≤ C := lgBesselCommonEnvelopeConstant_nonneg
  have hC : ∀ s' c' x' : ℝ, 1 ≤ c' * xiEndpointPhase s' x' →
      |lgBesselModel s' c' x'| ≤ C / Real.sqrt (c' * xiEndpointPhase s' x') ∧
      |lgBesselModel2 s' c' x'| ≤ C / Real.sqrt (c' * xiEndpointPhase s' x') :=
    fun s' c' x' hx' => lgBesselCommonEnvelopeConstant_spec s' c' x' hx'
  have hsub : Set.Icc A B ⊆ Set.Ioi 1 := fun t ht => lt_of_lt_of_le hA ht.1
  have hW : 0 < besselWronskian (c * xiEndpointPhase s A) :=
    besselWronskian_phase_pos hs0 hs1 hc hA
  set U := comparisonSol (prolateNormalFormSol R) s with hUdef
  set DU := comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s
    with hDUdef
  have hU : ∀ t ∈ Set.Icc A B, HasDerivAt U (DU t) t :=
    fun t ht => (radialProlate_comparison_pole_uniform hs0 hs1 (hsub ht) (hR t ht) (hDR t ht)
      (hode t ht)).1
  have hDU : ∀ t ∈ Set.Icc A B, HasDerivAt DU (-(lgFirstOrderCoeff s t) * DU t
      - (c ^ (2 : ℕ) * xiSpeed s t ^ (2 : ℕ) + lgNormalFormDefect s c (radialProlateQ s c) t) * U t) t :=
    fun t ht => (radialProlate_comparison_pole_uniform hs0 hs1 (hsub ht) (hR t ht) (hDR t ht)
      (hode t ht)).2.1
  have hcxit : ∀ t ∈ Set.Icc A B, 1 ≤ c * xiEndpointPhase s t := by
    intro t ht
    have hmono := xiEndpointPhase_le_of_le hs0 hs1 hA.le ht.1
    have := mul_le_mul_of_nonneg_left hmono hc.le
    linarith
  have hEnv : ∀ t ∈ Set.Icc A B,
      |lgBesselModel s c t| ≤ C / Real.sqrt (c * xiEndpointPhase s t)
        ∧ |lgBesselModel2 s c t| ≤ C / Real.sqrt (c * xiEndpointPhase s t) :=
    fun t ht => hC s c t (hcxit t ht)
  have hac : ContinuousOn (fun t : ℝ => lgNormalFormDefect s c (radialProlateQ s c) t)
      (Set.Icc A B) := (continuousOn_lgNormalFormDefect_radialProlate hs0 hs1).mono hsub
  -- the envelope bound on the solution, with the Volterra exponential estimated
  have hmainbound := abs_perturbed_le_lgEnvelope_mul_exp
    (a := fun t : ℝ => lgNormalFormDefect s c (radialProlateQ s c) t)
    hs0 hs1 hc hA hAB hC0 hcxi (fun y hy => hC s c y hy) hac hU hDU
  set S := |lgWeight s A * (U A * lgBesselModelDeriv s c A - DU A * lgBesselModel s c A)|
    + |lgWeight s A * (U A * lgBesselModel2Deriv s c A - DU A * lgBesselModel2 s c A)| with hSdef
  set K := S * Real.exp (2 * C ^ (2 : ℕ) / (c * besselWronskian (c * xiEndpointPhase s A)) * 127)
    / besselWronskian (c * xiEndpointPhase s A) with hKdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    positivity
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (mul_nonneg hS0 (Real.exp_nonneg _)) hW.le
  have hUb : ∀ t ∈ Set.Icc A B, |U t| ≤ C / Real.sqrt (c * xiEndpointPhase s t) * K := by
    intro t ht
    have hexp : (∫ u in A..t, 2 * (lgWeight s u
          * |lgNormalFormDefect s c (radialProlateQ s c) u|)
          * (C / Real.sqrt (c * xiEndpointPhase s u)) ^ (2 : ℕ)
          / besselWronskian (c * xiEndpointPhase s A))
        ≤ 2 * C ^ (2 : ℕ) / (c * besselWronskian (c * xiEndpointPhase s A)) * 127 :=
      integral_volterra_exponent_le hs0 hs1 hc hW hA ht.1
    have hE0 : 0 ≤ C / Real.sqrt (c * xiEndpointPhase s t) :=
      div_nonneg hC0 (Real.sqrt_nonneg _)
    refine le_trans (hmainbound t ht) ?_
    rw [hKdef]
    have hstep : Real.exp (∫ u in A..t, 2 * (lgWeight s u
          * |lgNormalFormDefect s c (radialProlateQ s c) u|)
          * (C / Real.sqrt (c * xiEndpointPhase s u)) ^ (2 : ℕ)
          / besselWronskian (c * xiEndpointPhase s A))
        ≤ Real.exp (2 * C ^ (2 : ℕ) / (c * besselWronskian (c * xiEndpointPhase s A)) * 127) :=
      Real.exp_le_exp.mpr hexp
    have hmul : S * Real.exp (∫ u in A..t, 2 * (lgWeight s u
          * |lgNormalFormDefect s c (radialProlateQ s c) u|)
          * (C / Real.sqrt (c * xiEndpointPhase s u)) ^ (2 : ℕ)
          / besselWronskian (c * xiEndpointPhase s A))
        ≤ S * Real.exp (2 * C ^ (2 : ℕ) / (c * besselWronskian (c * xiEndpointPhase s A)) * 127) :=
      mul_le_mul_of_nonneg_left hstep hS0
    have hdiv : C / Real.sqrt (c * xiEndpointPhase s t)
          / besselWronskian (c * xiEndpointPhase s A) * (S * Real.exp (∫ u in A..t,
            2 * (lgWeight s u * |lgNormalFormDefect s c (radialProlateQ s c) u|)
            * (C / Real.sqrt (c * xiEndpointPhase s u)) ^ (2 : ℕ)
            / besselWronskian (c * xiEndpointPhase s A)))
        = C / Real.sqrt (c * xiEndpointPhase s t)
          * (S * Real.exp (∫ u in A..t,
            2 * (lgWeight s u * |lgNormalFormDefect s c (radialProlateQ s c) u|)
            * (C / Real.sqrt (c * xiEndpointPhase s u)) ^ (2 : ℕ)
            / besselWronskian (c * xiEndpointPhase s A))
            / besselWronskian (c * xiEndpointPhase s A)) := by
      field_simp
    rw [hdiv]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hmul hW.le) hE0
  -- integrability of the two transport integrands and of the mass integrand
  have hUcont : ContinuousOn U (Set.Icc A B) :=
    fun t ht => ((hU t ht).continuousAt).continuousWithinAt
  have hprod : ∀ (V : ℝ → ℝ), ContinuousOn V (Set.Ioi 1) → ∀ x ∈ Set.Icc A B,
      IntervalIntegrable (fun t : ℝ => lgWeight s t
        * lgNormalFormDefect s c (radialProlateQ s c) t * (U t * V t)) MeasureTheory.volume A x := by
    intro V hV x hx
    have hxsub : Set.uIcc A x ⊆ Set.Icc A B := by
      rw [Set.uIcc_of_le hx.1]
      exact fun t ht => ⟨ht.1, le_trans ht.2 hx.2⟩
    have hIoi : Set.uIcc A x ⊆ Set.Ioi 1 := fun t ht => hsub (hxsub ht)
    exact (((((continuousOn_lgWeight hs0 hs1).mono hIoi).mul
      ((continuousOn_lgNormalFormDefect_radialProlate hs0 hs1).mono hIoi)).mul
      ((hUcont.mono hxsub).mul (hV.mono hIoi)))).intervalIntegrable
  refine ⟨C, K, hC0, rfl, hK0, hC, ?_, ?_⟩
  · rw [hKdef, hSdef, radialProlateVolterraK, radialProlateVolterraDatum]
  refine abs_perturbed_sub_model_le (a := fun t : ℝ => lgNormalFormDefect s c (radialProlateQ s c) t)
    (E := fun t : ℝ => C / Real.sqrt (c * xiEndpointPhase s t)) (K := K)
    (M := 127 * C ^ (2 : ℕ) / c) hs0 hs1 hc hA hAB hK0 (by positivity) hU hDU hEnv hUb
    (fun x hx => hprod (lgBesselModel s c) (continuousOn_lgBesselModel hs0) x hx)
    (fun x hx => hprod (lgBesselModel2 s c) (continuousOn_lgBesselModel2 hs0 hs1 hc) x hx)
    (fun x hx => intervalIntegrable_lgWeight_abs_defect_envelope hs0 hs1 hc hA hx.1)
    (fun x hx => integral_lgWeight_abs_defect_envelope_le hs0 hs1 hc hA hx.1)


end GaloisForLFunctions.RHTower

end
