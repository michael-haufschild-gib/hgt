import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimePowerEvenPartHarnack

/-!
# The odd-part payment of the first prime atom ends before `log 2`

For odd `F` supported in `[−r, r]`, `½ log 2 < r < log 2`, the atom of `2` couples `x ↔ log 2 − x` on
the strip `S₂ = [log 2 − r, r]`, and `∫ F F(· + log 2) = ∫_{S₂} α² − ∫_{S₂} ε²` with `α`, `ε` the parts
of `F` odd and even about `½ log 2`. Every micro-fold so far (sharp, shell, wide) pays the atom
through its odd part alone, from the surplus of the box `S₂ × S₂`:
`λ ∫_{S₂} α² ≤ ∫_{S₂} ∫_{S₂} k(x, y)(F x − F y)²` with `λ ≥ 2Λ(2)/√2 = √2 log 2 ≈ 0.980`.

Such a constant does not exist near `log 2` (`not_forall_oddPart_le_stripSurplus_logTwo`). The linear
profile `F(x) = x` has odd part `α(x) = x − ½ log 2`. On the full square `[0, a]²`, `a ≤ 1`, its box is
bounded by the majorant `|x − y|/2 − (x − y)²/(2(x + y)) + (x − y)²(x + y)/48 + (x − y)²(x + y)²/32`
(`t ω(t) ≤ ½ + t/4` on the distance, `ω ≥ ω₂` to second order on the sum, valid up to `2`), whose
square integral is `a³ − (4/3) a³ log 2 + a⁵/288 + a⁶/180` exactly (`integral_square_surplus_linear_le`).
Against `∫_0^a α² = a³/12` this is the quotient `12 − 16 log 2 + a²/24 + a³/15`: the regional
eigenvalue `2` of `1/(2|x − y|)` minus `6J`, `J = ∫∫_{[0,1]²} (x − y)²/(x + y) = (8 log 2 − 5)/3`, the
share of the reflected pairs `ω(x + y)`. At `a = log 2` it is `≈ 0.952 < √2 log 2`, and an inner
square only lowers the box (`integral_square_mono`), so the strict inequality holds on every strip
`[p, log 2 − p]`, `0 < p ≤ 1/400` (`linearProfile_stripBox_lt_firstAtom`).
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### `ω` to second order on `(0, 2]` -/

/-- `u ω(u) ≥ ½ + u/4 − u²/48 − u³/32` on `(0, 2]`. -/
theorem mul_archLevyDensity_ge_sharp_of_le_two {u : ℝ} (h0 : 0 < u) (h2 : u ≤ 2) :
    1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 ≤ u * archLevyDensity u := by
  set z := u / 2 with hz
  have hz0 : 0 < z := by rw [hz]; linarith
  obtain ⟨hs1, hs2, -, hc2⟩ := sinh_cosh_taylor_bounds hz0.le (by rw [hz]; linarith)
  have hS : 0 < Real.sinh z := by nlinarith [pow_pos hz0 3]
  have hC : 0 < Real.cosh z := Real.cosh_pos z
  rw [archLevyDensity_eq_inv_sinh_add_inv_cosh h0, ← hz]
  have e : u * (1 / (4 * Real.sinh z) + 1 / (4 * Real.cosh z)) =
      z / (2 * Real.sinh z) + z / (2 * Real.cosh z) := by
    rw [hz]; field_simp; ring
  rw [e]
  have k1 : (1 - z ^ 2 / 6) / 2 ≤ z / (2 * Real.sinh z) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have k2 : z / 2 * (1 - z ^ 2 / 2) ≤ z / (2 * Real.cosh z) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hc2 hz0.le]
  have hpoly : 1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 =
      (1 - z ^ 2 / 6) / 2 + z / 2 * (1 - z ^ 2 / 2) := by rw [hz]; ring
  linarith

/-! ### The majorant of the linear profile -/

/-- The majorant of the surplus integrand `k(x, y)(x − y)²` of the linear profile:
`|x − y|/2 − (x − y)²/(2(x + y)) + (x − y)²(x + y)/48 + (x − y)²(x + y)²/32`. -/
def linearProfileMajorant (x y : ℝ) : ℝ :=
  |x - y| / 2 - (x - y) ^ 2 / (x + y) / 2 + (x - y) ^ 2 * (x + y) / 48 +
    (x - y) ^ 2 * (x + y) ^ 2 / 32

/-- `k(x, y)(x − y)² ≤` the majorant on `[0, 1]²`: `t ω(t) ≤ ½ + t/4` at `t = |x − y|` and the
second-order lower bound of `ω` at `x + y ≤ 2`. -/
theorem surplusKernel_mul_sq_le_majorant {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1)
    (hy1 : y ≤ 1) : surplusKernel x y * (x - y) ^ 2 ≤ linearProfileMajorant x y := by
  unfold linearProfileMajorant
  rcases eq_or_ne x y with h | h
  · subst h; simp
  have hs : 0 < x + y := by
    by_contra hc; exact h (by linarith [not_lt.mp hc])
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr h)
  have hd1 : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 := mul_archLevyDensity_le hd hd1
  have h2 := mul_archLevyDensity_ge_sharp_of_le_two hs (by linarith)
  have k1 : archLevyDensity |x - y| * (x - y) ^ 2 ≤ |x - y| / 2 + (x - y) ^ 2 / 4 := by
    rw [← sq_abs (x - y)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hd.le]
  have k2 : (x - y) ^ 2 / (x + y) / 2 + (x - y) ^ 2 / 4 - (x - y) ^ 2 * (x + y) / 48 -
      (x - y) ^ 2 * (x + y) ^ 2 / 32 ≤ archLevyDensity (x + y) * (x - y) ^ 2 := by
    have e1 : (x - y) ^ 2 / (x + y) / 2 + (x - y) ^ 2 / 4 - (x - y) ^ 2 * (x + y) / 48 -
        (x - y) ^ 2 * (x + y) ^ 2 / 32 =
        (x - y) ^ 2 / (x + y) * (1 / 2 + (x + y) / 4 - (x + y) ^ 2 / 48 - (x + y) ^ 3 / 32) := by
      field_simp
    have e2 : archLevyDensity (x + y) * (x - y) ^ 2 =
        (x - y) ^ 2 / (x + y) * ((x + y) * archLevyDensity (x + y)) := by
      field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h2 (div_nonneg (sq_nonneg _) hs.le)
  unfold surplusKernel
  rw [sub_mul]
  linarith [k1, k2]

/-- The surplus integrand of the linear profile is nonnegative and at most `1` on `[0, 1]²`. -/
theorem surplusKernel_mul_sq_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1)
    (hy1 : y ≤ 1) : 0 ≤ surplusKernel x y * (x - y) ^ 2 ∧ surplusKernel x y * (x - y) ^ 2 ≤ 1 := by
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne x y with h | h
    · subst h; simp
    rcases eq_or_lt_of_le hx with h0 | h0
    · subst h0; unfold surplusKernel; rw [zero_sub, abs_neg, abs_of_nonneg hy, zero_add]; simp
    rcases eq_or_lt_of_le hy with h0' | h0'
    · subst h0'; unfold surplusKernel; rw [sub_zero, abs_of_nonneg hx, add_zero]; simp
    exact mul_nonneg (surplusKernel_nonneg h0 h0' h) (sq_nonneg _)
  · refine (surplusKernel_mul_sq_le_majorant hx hy hx1 hy1).trans ?_
    unfold linearProfileMajorant
    have hd : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hd2 : (x - y) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (x - y)]
    have hq : 0 ≤ (x - y) ^ 2 / (x + y) / 2 := by positivity
    have h3 : (x - y) ^ 2 * (x + y) ≤ 2 := by nlinarith [sq_nonneg (x - y)]
    have h4 : (x - y) ^ 2 * (x + y) ^ 2 ≤ 4 := by
      have : (x + y) ^ 2 ≤ 4 := by nlinarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    linarith

/-! ### Rows of the majorant -/

theorem integral_abs_sub_linearRow {a x : ℝ} (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫ y in (0 : ℝ)..a, |x - y|) = x ^ 2 / 2 + (a - x) ^ 2 / 2 := by
  have hc : Continuous fun y : ℝ => |x - y| := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x) (hc.intervalIntegrable 0 x)
    (hc.intervalIntegrable x a)]
  have e1 : (∫ y in (0 : ℝ)..x, |x - y|) = ∫ y in (0 : ℝ)..x, (x - y) :=
    intervalIntegral.integral_congr fun y hy => by
      rw [uIcc_of_le hx0] at hy
      simp only [abs_of_nonneg (by linarith [hy.2] : (0 : ℝ) ≤ x - y)]
  have e2 : (∫ y in x..a, |x - y|) = ∫ y in x..a, (y - x) :=
    intervalIntegral.integral_congr fun y hy => by
      rw [uIcc_of_le hxa] at hy
      simp only [abs_of_nonpos (by linarith [hy.1] : x - y ≤ 0), neg_sub]
  rw [e1, e2, integral_deriv_eq_sub' (fun y => x * y - y ^ 2 / 2)
      (by funext y; simp (disch := fun_prop); ring) (fun y _ => by fun_prop) (by fun_prop),
    integral_deriv_eq_sub' (fun y => y ^ 2 / 2 - x * y)
      (by funext y; simp (disch := fun_prop); ring) (fun y _ => by fun_prop) (by fun_prop)]
  ring

/-- `∫_0^a (x − y)²/(x + y) dy = ((x + a)² − x²)/2 − 4xa + 4x² log((x + a)/x)` for `x > 0`. -/
theorem integral_sq_sub_div_add_linearRow {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) :
    (∫ y in (0 : ℝ)..a, (x - y) ^ 2 / (x + y)) =
      ((x + a) ^ 2 - x ^ 2) / 2 - 4 * x * a + 4 * x ^ 2 * (Real.log (x + a) - Real.log x) := by
  have hpos : ∀ y ∈ uIcc 0 a, 0 < x + y := fun y hy => by
    rw [uIcc_of_le ha] at hy; linarith [hy.1]
  rw [integral_eq_sub_of_hasDerivAt
    (f := fun y => (x + y) ^ 2 / 2 - 4 * x * (x + y) + 4 * x ^ 2 * Real.log (x + y))
    (f' := fun y => (x - y) ^ 2 / (x + y)) (fun y hy => by
      have h1 : HasDerivAt (fun y => x + y) 1 y := (hasDerivAt_id y).const_add x
      have h := (((h1.pow 2).div_const 2).sub (h1.const_mul (4 * x))).add
        ((h1.log (hpos y hy).ne').const_mul (4 * x ^ 2))
      refine h.congr_deriv ?_
      have := (hpos y hy).ne'
      field_simp
      ring)
    (ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun y hy => (hpos y hy).ne'))]
  simp only [add_zero]
  ring

theorem integral_sq_sub_mul_add_linearRow (a x : ℝ) :
    (∫ y in (0 : ℝ)..a, (x - y) ^ 2 * (x + y)) =
      x ^ 3 * a - x ^ 2 * a ^ 2 / 2 - x * a ^ 3 / 3 + a ^ 4 / 4 := by
  rw [integral_deriv_eq_sub' (fun y => x ^ 3 * y - x ^ 2 * y ^ 2 / 2 - x * y ^ 3 / 3 + y ^ 4 / 4)
    (by funext y; simp (disch := fun_prop); ring) (fun y _ => by fun_prop) (by fun_prop)]
  ring

theorem integral_sq_sub_mul_sq_add_linearRow (a x : ℝ) :
    (∫ y in (0 : ℝ)..a, (x - y) ^ 2 * (x + y) ^ 2) = x ^ 4 * a - 2 * x ^ 2 * a ^ 3 / 3 + a ^ 5 / 5 := by
  rw [integral_deriv_eq_sub' (fun y => x ^ 4 * y - 2 * x ^ 2 * y ^ 3 / 3 + y ^ 5 / 5)
    (by funext y; simp (disch := fun_prop); ring) (fun y _ => by fun_prop) (by fun_prop)]
  ring

/-- The row integral of the majorant, `x ∈ (0, a]`. -/
def linearProfileRow (a x : ℝ) : ℝ :=
  (x ^ 2 / 2 + (a - x) ^ 2 / 2) / 2 -
    (((x + a) ^ 2 - x ^ 2) / 2 - 4 * x * a + 4 * x ^ 2 * (Real.log (x + a) - Real.log x)) / 2 +
    (x ^ 3 * a - x ^ 2 * a ^ 2 / 2 - x * a ^ 3 / 3 + a ^ 4 / 4) / 48 +
    (x ^ 4 * a - 2 * x ^ 2 * a ^ 3 / 3 + a ^ 5 / 5) / 32

theorem integral_linearProfileMajorant_row {a x : ℝ} (hx : 0 < x) (hxa : x ≤ a) :
    (∫ y in (0 : ℝ)..a, linearProfileMajorant x y) = linearProfileRow a x := by
  have ha : 0 ≤ a := by linarith
  have hpos : ∀ y ∈ uIcc 0 a, 0 < x + y := fun y hy => by
    rw [uIcc_of_le ha] at hy; linarith [hy.1]
  have i1 : IntervalIntegrable (fun y => |x - y| / 2) volume 0 a :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun y => (x - y) ^ 2 / (x + y) / 2) volume 0 a :=
    ContinuousOn.intervalIntegrable (ContinuousOn.div_const (ContinuousOn.div (by fun_prop)
      (by fun_prop) fun y hy => (hpos y hy).ne') _)
  have i3 : IntervalIntegrable (fun y => (x - y) ^ 2 * (x + y) / 48) volume 0 a :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i4 : IntervalIntegrable (fun y => (x - y) ^ 2 * (x + y) ^ 2 / 32) volume 0 a :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  unfold linearProfileMajorant
  rw [intervalIntegral.integral_add ((i1.sub i2).add i3) i4, intervalIntegral.integral_add (i1.sub i2) i3,
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_div, intervalIntegral.integral_div, integral_abs_sub_linearRow hx.le hxa,
    integral_sq_sub_div_add_linearRow ha hx, integral_sq_sub_mul_add_linearRow, integral_sq_sub_mul_sq_add_linearRow]
  rfl

/-! ### The square integral of the majorant -/

theorem integral_sq_mul_log_zero_to {a : ℝ} (ha : 0 ≤ a) :
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.log x) = a ^ 3 / 3 * Real.log a - a ^ 3 / 9 := by
  have hc : Continuous fun x : ℝ => x ^ 2 * Real.log x := by
    have e : (fun x : ℝ => x ^ 2 * Real.log x) = fun x => x * (x * Real.log x) := by funext x; ring
    rw [e]; exact continuous_id.mul Real.continuous_mul_log
  have hF : ContinuousOn (fun x : ℝ => x ^ 3 / 3 * Real.log x - x ^ 3 / 9) (Icc 0 a) := by
    have e : (fun x : ℝ => x ^ 3 / 3 * Real.log x - x ^ 3 / 9) =
        fun x => x ^ 2 * (x * Real.log x) / 3 - x ^ 3 / 9 := by funext x; ring
    rw [e]
    exact ((((continuous_pow 2).mul Real.continuous_mul_log).div_const 3).sub
      ((continuous_pow 3).div_const 9)).continuousOn
  rw [integral_eq_sub_of_hasDerivAt_of_le ha (f := fun x => x ^ 3 / 3 * Real.log x - x ^ 3 / 9)
    (f' := fun x => x ^ 2 * Real.log x) hF
    (fun x hx => by
      have hx0 : x ≠ 0 := hx.1.ne'
      have h := (((hasDerivAt_pow 3 x).div_const 3).mul (Real.hasDerivAt_log hx0)).sub
        ((hasDerivAt_pow 3 x).div_const 9)
      refine h.congr_deriv ?_
      field_simp
      ring)
    (hc.intervalIntegrable _ _)]
  simp

theorem integral_sq_mul_log_add_self {a : ℝ} (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, x ^ 2 * Real.log (x + a)) =
      2 * a ^ 3 / 3 * Real.log (2 * a) - a ^ 3 / 3 * Real.log a - 5 * a ^ 3 / 18 := by
  have hpos : ∀ x ∈ uIcc 0 a, 0 < x + a := fun x hx => by
    rw [uIcc_of_le ha.le] at hx; linarith [hx.1]
  rw [integral_eq_sub_of_hasDerivAt
    (f := fun x => (x ^ 3 + a ^ 3) / 3 * Real.log (x + a) - x ^ 3 / 9 + a * x ^ 2 / 6 - a ^ 2 * x / 3)
    (f' := fun x => x ^ 2 * Real.log (x + a))
    (fun x hx => by
      have h1 : HasDerivAt (fun x => x + a) 1 x := (hasDerivAt_id x).add_const a
      have hne := (hpos x hx).ne'
      have h := ((((((hasDerivAt_pow 3 x).add_const (a ^ 3)).div_const 3).mul (h1.log hne)).sub
        ((hasDerivAt_pow 3 x).div_const 9)).add (((hasDerivAt_pow 2 x).const_mul a).div_const 6)).sub
        (((hasDerivAt_id x).const_mul (a ^ 2)).div_const 3)
      refine h.congr_deriv ?_
      field_simp
      ring)
    (ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop)
      (ContinuousOn.log (by fun_prop) fun x hx => (hpos x hx).ne')))]
  rw [show a + a = 2 * a by ring]
  simp only [zero_add]
  ring

/-- The polynomial part of the row integral. -/
def linearProfileRowPoly (a x : ℝ) : ℝ :=
  (x ^ 2 / 2 + (a - x) ^ 2 / 2) / 2 - (((x + a) ^ 2 - x ^ 2) / 2 - 4 * x * a) / 2 +
    (x ^ 3 * a - x ^ 2 * a ^ 2 / 2 - x * a ^ 3 / 3 + a ^ 4 / 4) / 48 +
    (x ^ 4 * a - 2 * x ^ 2 * a ^ 3 / 3 + a ^ 5 / 5) / 32

theorem linearProfileRow_eq (a x : ℝ) :
    linearProfileRow a x = linearProfileRowPoly a x - 2 * (x ^ 2 * Real.log (x + a)) + 2 * (x ^ 2 * Real.log x) := by
  unfold linearProfileRow linearProfileRowPoly; ring

theorem integral_linearProfileRowPoly (a : ℝ) :
    (∫ x in (0 : ℝ)..a, linearProfileRowPoly a x) = 2 * a ^ 3 / 3 + a ^ 5 / 288 + a ^ 6 / 180 := by
  unfold linearProfileRowPoly
  rw [integral_deriv_eq_sub' (fun x => x ^ 3 / 12 - (a - x) ^ 3 / 12 - (x + a) ^ 3 / 12 + x ^ 3 / 12 +
      a * x ^ 2 + (x ^ 4 * a / 4 - x ^ 3 * a ^ 2 / 6 - x ^ 2 * a ^ 3 / 6 + a ^ 4 * x / 4) / 48 +
      (x ^ 5 * a / 5 - 2 * x ^ 3 * a ^ 3 / 9 + a ^ 5 * x / 5) / 32)
    (by funext x; simp (disch := fun_prop); ring) (fun x _ => by fun_prop) (by fun_prop)]
  ring

/-- **The square integral of the majorant**: `∫_0^a ∫_0^a = a³ − (4/3) a³ log 2 + a⁵/288 + a⁶/180`.
The logarithms of `a` cancel; `log 2` comes from `∫_0^a x² log((x + a)/x) dx`. -/
theorem integral_linearProfileRow {a : ℝ} (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, linearProfileRow a x) =
      a ^ 3 - 4 * a ^ 3 / 3 * Real.log 2 + a ^ 5 / 288 + a ^ 6 / 180 := by
  have hpos : ∀ x ∈ uIcc 0 a, 0 < x + a := fun x hx => by
    rw [uIcc_of_le ha.le] at hx; linarith [hx.1]
  have i1 : IntervalIntegrable (fun x => linearProfileRowPoly a x) volume 0 a := by
    unfold linearProfileRowPoly; exact Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun x => 2 * (x ^ 2 * Real.log (x + a))) volume 0 a :=
    (ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop)
      (ContinuousOn.log (by fun_prop) fun x hx => (hpos x hx).ne'))).const_mul 2
  have i3 : IntervalIntegrable (fun x => 2 * (x ^ 2 * Real.log x)) volume 0 a := by
    have e : (fun x : ℝ => x ^ 2 * Real.log x) = fun x => x * (x * Real.log x) := by funext x; ring
    have hc : Continuous fun x : ℝ => x ^ 2 * Real.log x := by
      rw [e]; exact continuous_id.mul Real.continuous_mul_log
    exact (hc.intervalIntegrable _ _).const_mul 2
  have e : (fun x => linearProfileRow a x) =
      fun x => linearProfileRowPoly a x - 2 * (x ^ 2 * Real.log (x + a)) + 2 * (x ^ 2 * Real.log x) :=
    funext fun x => linearProfileRow_eq a x
  rw [e, intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_linearProfileRowPoly,
    integral_sq_mul_log_add_self ha, integral_sq_mul_log_zero_to ha.le, Real.log_mul (by norm_num) ha.ne']
  ring

theorem linearProfileRow_zero (a : ℝ) : linearProfileRow a 0 = a ^ 4 / 192 + a ^ 5 / 160 := by
  unfold linearProfileRow; simp; ring

/-- **The box of the linear profile on `[0, a]`**, `0 < a ≤ 1`:
`∫_0^a ∫_0^a k(x, y)(x − y)² ≤ a³ − (4/3) a³ log 2 + a⁵/288 + a⁶/180`. -/
theorem integral_square_surplus_linear_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..a, surplusKernel x y * (x - y) ^ 2) ≤
      a ^ 3 - 4 * a ^ 3 / 3 * Real.log 2 + a ^ 5 / 288 + a ^ 6 / 180 := by
  have hmeas : Measurable (Function.uncurry fun x y : ℝ => surplusKernel x y * (x - y) ^ 2) :=
    measurable_stripIntegrand continuous_id
  have hb : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, |(fun x y : ℝ => surplusKernel x y * (x - y) ^ 2) x y| ≤ 1 :=
    fun x hx y hy => by
      obtain ⟨h0, h1⟩ := surplusKernel_mul_sq_bounds hx.1 hy.1 (hx.2.trans ha1) (hy.2.trans ha1)
      simp only; rw [abs_of_nonneg h0]; exact h1
  obtain ⟨hi, ho⟩ := intervalIntegrable_iterated ha.le hmeas hb
  have hrow : IntervalIntegrable (fun x => linearProfileRow a x) volume 0 a := by
    have hpos : ∀ x ∈ uIcc 0 a, 0 < x + a := fun x hx => by
      rw [uIcc_of_le ha.le] at hx; linarith [hx.1]
    have e : (fun x => linearProfileRow a x) =
        fun x => linearProfileRowPoly a x - 2 * (x ^ 2 * Real.log (x + a)) + 2 * (x * (x * Real.log x)) :=
      funext fun x => by rw [linearProfileRow_eq]; ring
    rw [e]
    refine ((Continuous.intervalIntegrable (by unfold linearProfileRowPoly; fun_prop) _ _).sub
      ((ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop)
        (ContinuousOn.log (by fun_prop) fun x hx => (hpos x hx).ne'))).const_mul 2)).add
      (((continuous_id.mul Real.continuous_mul_log).intervalIntegrable _ _).const_mul 2)
  rw [← integral_linearProfileRow ha]
  refine intervalIntegral.integral_mono_on ha.le ho hrow fun x hx => ?_
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · subst h0
    have e : (∫ y in (0 : ℝ)..a, surplusKernel 0 y * (0 - y) ^ 2) = ∫ _ in (0 : ℝ)..a, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le ha.le] at hy
      unfold surplusKernel
      rw [zero_sub, abs_neg, abs_of_nonneg hy.1, zero_add, sub_self, zero_mul]
    rw [intervalIntegral.integral_zero] at e
    rw [e, linearProfileRow_zero]; positivity
  · rw [← integral_linearProfileMajorant_row h0 hx.2]
    have hpos : ∀ y ∈ uIcc 0 a, 0 < x + y := fun y hy => by
      rw [uIcc_of_le ha.le] at hy; linarith [hy.1]
    have hmaj : IntervalIntegrable (fun y => linearProfileMajorant x y) volume 0 a := by
      unfold linearProfileMajorant
      exact ((((Continuous.intervalIntegrable (by fun_prop) _ _).sub (ContinuousOn.intervalIntegrable
        (ContinuousOn.div_const (ContinuousOn.div (by fun_prop) (by fun_prop)
          fun y hy => (hpos y hy).ne') _))).add (Continuous.intervalIntegrable (by fun_prop) _ _)).add
        (Continuous.intervalIntegrable (by fun_prop) _ _))
    exact intervalIntegral.integral_mono_on ha.le (hi x hx) hmaj fun y hy =>
      surplusKernel_mul_sq_le_majorant hx.1 hy.1 (hx.2.trans ha1) (hy.2.trans ha1)

/-! ### Inner squares and the wall -/

/-- A nonnegative bounded integrand has a smaller box integral on an inner square. -/
theorem integral_square_mono {f : ℝ → ℝ → ℝ} {a c d C : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hda : d ≤ a)
    (hf : Measurable (Function.uncurry f)) (hb : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, |f x y| ≤ C)
    (h0 : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, 0 ≤ f x y) :
    (∫ x in c..d, ∫ y in c..d, f x y) ≤ ∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..a, f x y := by
  have ha : 0 ≤ a := hc.trans (hcd.trans hda)
  have hsub : ∀ x ∈ Icc c d, x ∈ Icc 0 a := fun x hx => ⟨hc.trans hx.1, hx.2.trans hda⟩
  obtain ⟨hi, ho⟩ := intervalIntegrable_iterated ha hf hb
  obtain ⟨-, ho'⟩ := intervalIntegrable_iterated hcd hf fun x hx y hy => hb x (hsub x hx) y (hsub y hy)
  have hnn : ∀ x ∈ Icc 0 a, 0 ≤ᵐ[volume.restrict (Ioc 0 a)] f x := fun x hx =>
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy =>
      h0 x hx y ⟨hy.1.le, hy.2⟩)
  calc (∫ x in c..d, ∫ y in c..d, f x y) ≤ ∫ x in c..d, ∫ y in (0 : ℝ)..a, f x y :=
        intervalIntegral.integral_mono_on hcd ho'
          (ho.mono_set (by rw [uIcc_of_le hcd, uIcc_of_le ha]; exact Icc_subset_Icc hc hda))
          fun x hx => intervalIntegral.integral_mono_interval hc hcd hda (hnn x (hsub x hx))
            (hi x (hsub x hx))
    _ ≤ ∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..a, f x y :=
        intervalIntegral.integral_mono_interval hc hcd hda
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx =>
            intervalIntegral.integral_nonneg ha fun y hy => h0 x ⟨hx.1.le, hx.2⟩ y hy)) ho

/-- The odd part of the linear profile about `L/2` has `∫_p^{L−p} α² = (L − 2p)³/12`. -/
theorem integral_reflectedOddPart_id_sq (L p : ℝ) :
    (∫ x in p..(L - p), reflectedOddPart (fun x => x) L x ^ 2) = (L - 2 * p) ^ 3 / 12 := by
  unfold reflectedOddPart
  rw [integral_deriv_eq_sub' (fun x => (x - L / 2) ^ 3 / 3)
    (by funext x; simp (disch := fun_prop); ring) (fun x _ => by fun_prop) (by fun_prop)]
  ring

/-- **The odd-part payment of the first prime atom fails near `log 2`.** For `0 < p ≤ 1/400`, i.e.
on the strip `S₂ = [p, log 2 − p]` of the window `r = log 2 − p`, the linear profile `F(x) = x` has
box surplus below `2Λ(2)/√2` times its odd part:

    ∫_{S₂} ∫_{S₂} k(x, y)(x − y)² < 2 Λ(2)/√2 ∫_{S₂} α²,   α(x) = x − log 2/2.

The box is at most that of `[0, log 2]`, which is `≤ L³ − (4/3)L⁴ + L⁵/288 + L⁶/180`, `L = log 2`
(`integral_square_surplus_linear_le`): the reflected pairs `ω(x + y)` remove `6J = 2(8 log 2 − 5)` of
the regional eigenvalue `2`, leaving `12 − 16 log 2 + O(L²) ≈ 0.952 < √2 log 2`. -/
theorem linearProfile_stripBox_lt_firstAtom {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 400) :
    (∫ x in p..(Real.log 2 - p), ∫ y in p..(Real.log 2 - p), surplusKernel x y * (x - y) ^ 2) <
      2 * vonMangoldtAtom 2 * ∫ x in p..(Real.log 2 - p),
        reflectedOddPart (fun x => x) (Real.log 2) x ^ 2 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have hΛ := vonMangoldtAtom_two_ge
  set L := Real.log 2 with hL
  have hL0 : 0 < L := by linarith
  have hmeas : Measurable (Function.uncurry fun x y : ℝ => surplusKernel x y * (x - y) ^ 2) :=
    measurable_stripIntegrand continuous_id
  have hmono := integral_square_mono (f := fun x y : ℝ => surplusKernel x y * (x - y) ^ 2) (a := L)
    (c := p) (d := L - p) (C := 1) hp0.le (by linarith) (by linarith) hmeas
    (fun x hx y hy => by
      obtain ⟨h0, h1⟩ := surplusKernel_mul_sq_bounds hx.1 hy.1 (by linarith [hx.2])
        (by linarith [hy.2])
      rw [abs_of_nonneg h0]; exact h1)
    (fun x hx y hy => (surplusKernel_mul_sq_bounds hx.1 hy.1 (by linarith [hx.2])
      (by linarith [hy.2])).1)
  have hbox := integral_square_surplus_linear_le hL0 (by linarith)
  rw [integral_reflectedOddPart_id_sq]
  rw [← hL] at hbox
  -- `L³ − (4/3)L⁴ + L⁵/288 + L⁶/180 < (49/50)(L − 2p)³/12`
  have k3 : L ^ 3 ≤ (0.6931471808 : ℝ) ^ 3 := pow_le_pow_left₀ hL0.le h2.le 3
  have k4 : (0.6931471803 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) h1.le 4
  have k5 : L ^ 5 ≤ (0.6931471808 : ℝ) ^ 5 := pow_le_pow_left₀ hL0.le h2.le 5
  have k6 : L ^ 6 ≤ (0.6931471808 : ℝ) ^ 6 := pow_le_pow_left₀ hL0.le h2.le 6
  have kq : ((0.6931471803 : ℝ) - 1 / 200) ^ 3 ≤ (L - 2 * p) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have e4 : 4 * L ^ 3 / 3 * L = 4 * L ^ 4 / 3 := by ring
  have hq0 : 0 ≤ (L - 2 * p) ^ 3 / 12 := by
    have : 0 ≤ L - 2 * p := by linarith
    positivity
  have hA := mul_le_mul_of_nonneg_right (show 49 / 50 ≤ 2 * vonMangoldtAtom 2 by linarith) hq0
  norm_num at k3 k4 k5 k6 kq
  rw [e4] at hbox
  linarith

/-- In the language of the strip surplus: `2 stripSurplus_{S₂}(x) < 2Λ(2)/√2 ∫_{S₂} α²`. -/
theorem two_mul_stripSurplus_id_lt_firstAtom {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 400) :
    2 * stripSurplus (fun x => x) p (Real.log 2 - p) <
      2 * vonMangoldtAtom 2 * ∫ x in p..(Real.log 2 - p),
        reflectedOddPart (fun x => x) (Real.log 2) x ^ 2 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  rw [← integral_strip_eq_two_mul_stripSurplus (F := fun x => x) (K := 1) continuous_id'
    (fun a b => by simp) hp0 (by linarith) (by linarith)]
  exact linearProfile_stripBox_lt_firstAtom hp0 hp

/-- **No odd-part estimate pays the first prime atom from its own strip near `log 2`.** On the
window `r = log 2 − p`, `0 < p ≤ 1/400`, there is no inequality
`2Λ(2)/√2 ∫_{S₂} α_F² ≤ 2 stripSurplus_{S₂}(F)` for all Lipschitz `F`: the sharp, wide and shell
micro-folds, and every other fold of `S₂ × S₂` that bounds the odd part alone, stop before `log 2`. -/
theorem not_forall_oddPart_le_stripSurplus_logTwo {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 400) :
    ¬ ∀ F : ℝ → ℝ, Continuous F → (∃ K, ∀ a b, |F a - F b| ≤ K * |a - b|) →
      2 * vonMangoldtAtom 2 * (∫ x in p..(Real.log 2 - p), reflectedOddPart F (Real.log 2) x ^ 2) ≤
        2 * stripSurplus F p (Real.log 2 - p) := fun h =>
  absurd (h (fun x => x) continuous_id ⟨1, fun a b => by simp⟩)
    (not_le.mpr (two_mul_stripSurplus_id_lt_firstAtom hp0 hp))

end GaloisForLFunctions.ArithmeticIncidencePositivity
