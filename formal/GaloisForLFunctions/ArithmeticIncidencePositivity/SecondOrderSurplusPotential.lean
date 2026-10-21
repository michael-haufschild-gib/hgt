import GaloisForLFunctions.ArithmeticIncidencePositivity.QuarticGaugeSurplusPotential
import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeArchimedeanBounds

/-!
# The surplus potential to second order, and the sharper antiderivative

`QuarticGaugeSurplusPotential` bounds the surplus kernel `k(x, y) = ω(|x − y|) − ω(x + y)` by its
principal part `1/(2|x − y|) − 1/(2(x + y))` up to `(x + y)/16 + (x + y)²/32`, and charges the error
`L ∫ ((x + y)/16 + (x + y)²/32)|x − y|`. Both kernels are known to second order:

    ω₂(u) ≤ ω(u) ≤ ω₂(u) + u³/250,   ω₂(u) = 1/(2u) + 1/4 − u/48 − u²/32,   0 < u ≤ 3/4

(`archLevyDensity_secondOrder_bounds`; the lower bound is `mul_archLevyDensity_ge_sharp`). Hence

    k(x, y) = k₀(x, y) + (x + y − |x − y|)/48 + xy/8 + O((x + y)³/250)

(`abs_surplusKernel_sub_secondOrder_le`): the first correction is `min(x, y)/24 + xy/8`, nonnegative,
and its integral against the differences of a quartic gauge is an explicit polynomial
(`integral_firstOrder_quarticGauge`, `firstOrderSurplus`). The error is `O(r⁵)`, so the cost of the
curvature of `ω` drops from `L · O(r³)` to `L · (4/125) r⁵` (`mul_surplusPotential_quarticGauge_ge_second`).

The antiderivative `Ω` gains its second-order term as well:
`Ω(y) ≥ −½ log(y/4) + π/4 − y/4 + y²/96` on `(0, 1]` (`archLevyAntideriv_ge_second`), from
`log(z coth z) ≥ z²/3 − 7z⁴/36` and `tanh z ≤ z − z³/3 + z⁵/5`, `z = y/4`.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The Lévy density to second order -/

/-- `cosh z ≥ 1 + z²/2 + z⁴/24 − z⁶/300` on `[0, 1]`. -/
theorem cosh_ge_taylor_four {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    1 + z ^ 2 / 2 + z ^ 4 / 24 - z ^ 6 / 300 ≤ Real.cosh z := by
  have hz : |z| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  have hzn : |-z| ≤ 1 := by rwa [abs_neg]
  have hp := taylor_six_le_exp hz
  have hm := taylor_six_le_exp hzn
  rw [abs_of_nonneg h0] at hp
  rw [abs_neg, abs_of_nonneg h0] at hm
  have h6 : 0 ≤ z ^ 6 := by positivity
  rw [Real.cosh_eq]
  nlinarith

/-- **Second-order upper bound** `u ω(u) ≤ ½ + u/4 − u²/48 − u³/32 + u⁴/250` on `(0, 3/4]`. -/
theorem mul_archLevyDensity_le_second {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 3 / 4) :
    u * archLevyDensity u ≤ 1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 + u ^ 4 / 250 := by
  set z := u / 2 with hz
  have hz0 : 0 < z := by rw [hz]; linarith
  have hz1 : z ≤ 3 / 8 := by rw [hz]; linarith
  obtain ⟨hs1, -, -, -⟩ := sinh_cosh_taylor_bounds hz0.le (by linarith)
  have hc := cosh_ge_taylor_four hz0.le (by linarith)
  have hS : 0 < Real.sinh z := by nlinarith [pow_pos hz0 3]
  have hC : 0 < Real.cosh z := Real.cosh_pos z
  rw [archLevyDensity_eq_inv_sinh_add_inv_cosh h0, ← hz]
  have e : u * (1 / (4 * Real.sinh z) + 1 / (4 * Real.cosh z)) =
      z / (2 * Real.sinh z) + z / (2 * Real.cosh z) := by
    rw [hz]; field_simp; ring
  rw [e]
  have hA : 0 ≤ 1 - z ^ 2 / 6 + z ^ 4 / 36 := by nlinarith [sq_nonneg (z ^ 2 / 6 - 1 / 2)]
  have k1 : z / (2 * Real.sinh z) ≤ (1 - z ^ 2 / 6 + z ^ 4 / 36) / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs1 hA, pow_pos hz0 7]
  have hB : 0 ≤ 1 - z ^ 2 / 2 + 5 * z ^ 4 / 24 + z ^ 6 / 20 := by
    nlinarith [sq_nonneg (z ^ 2 / 2 - 1 / 2), pow_nonneg hz0.le 6, pow_nonneg hz0.le 4]
  have hprod : 1 ≤ (1 - z ^ 2 / 2 + 5 * z ^ 4 / 24 + z ^ 6 / 20) *
      (1 + z ^ 2 / 2 + z ^ 4 / 24 - z ^ 6 / 300) := by
    have h2 : z ^ 2 ≤ 9 / 64 := by nlinarith
    nlinarith [pow_nonneg hz0.le 6, pow_nonneg hz0.le 8, pow_nonneg hz0.le 10, pow_nonneg hz0.le 12,
      mul_nonneg (pow_nonneg hz0.le 6) (by linarith : (0 : ℝ) ≤ 9 / 64 - z ^ 2)]
  have k2 : z / (2 * Real.cosh z) ≤ z / 2 * (1 - z ^ 2 / 2 + 5 * z ^ 4 / 24 + z ^ 6 / 20) := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hc (mul_nonneg hz0.le hB)
    nlinarith
  have hpoly : (1 - z ^ 2 / 6 + z ^ 4 / 36) / 2 + z / 2 * (1 - z ^ 2 / 2 + 5 * z ^ 4 / 24 + z ^ 6 / 20) ≤
      1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 + u ^ 4 / 250 := by
    rw [hz]
    nlinarith [pow_pos h0 4, mul_nonneg (pow_pos h0 4).le (by linarith : (0 : ℝ) ≤ 3 / 4 - u),
      mul_nonneg (pow_pos h0 5).le (by linarith : (0 : ℝ) ≤ 3 / 4 - u), pow_pos h0 5, pow_pos h0 7]
  linarith

/-- **The Lévy density to second order.** On `(0, 3/4]`,
`ω₂(u) ≤ ω(u) ≤ ω₂(u) + u³/250`, `ω₂(u) = 1/(2u) + 1/4 − u/48 − u²/32`. -/
theorem archLevyDensity_secondOrder_bounds {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 3 / 4) :
    1 / (2 * u) + 1 / 4 - u / 48 - u ^ 2 / 32 ≤ archLevyDensity u ∧
      archLevyDensity u ≤ 1 / (2 * u) + 1 / 4 - u / 48 - u ^ 2 / 32 + u ^ 3 / 250 := by
  have hlo := mul_archLevyDensity_ge_sharp h0 (by linarith)
  have hhi := mul_archLevyDensity_le_second h0 h1
  have e1 : 1 / (2 * u) + 1 / 4 - u / 48 - u ^ 2 / 32 =
      (1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32) / u := by field_simp
  have e2 : 1 / (2 * u) + 1 / 4 - u / 48 - u ^ 2 / 32 + u ^ 3 / 250 =
      (1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 + u ^ 4 / 250) / u := by field_simp
  refine ⟨?_, ?_⟩
  · rw [e1, div_le_iff₀ h0]; linarith
  · rw [e2, le_div_iff₀ h0]; linarith

/-- **The surplus kernel to second order.** For `x, y > 0`, `x ≠ y`, `x + y ≤ 3/4`:
`|k(x, y) − (1/(2|x − y|) − 1/(2(x + y))) − ((x + y − |x − y|)/48 + xy/8)| ≤ (x + y)³/250`. -/
theorem abs_surplusKernel_sub_secondOrder_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y)
    (hs : x + y ≤ 3 / 4) :
    |surplusKernel x y - (1 / (2 * |x - y|) - 1 / (2 * (x + y))) -
        ((x + y - |x - y|) / 48 + x * y / 8)| ≤ (x + y) ^ 3 / 250 := by
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hdle : |x - y| ≤ x + y := by rw [abs_le]; constructor <;> linarith
  obtain ⟨a1, a2⟩ := archLevyDensity_secondOrder_bounds hd (by linarith)
  obtain ⟨b1, b2⟩ := archLevyDensity_secondOrder_bounds (show 0 < x + y by linarith) hs
  have hsq : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs _
  have hcube : |x - y| ^ 3 ≤ (x + y) ^ 3 := pow_le_pow_left₀ hd.le hdle 3
  have hc0 : 0 ≤ |x - y| ^ 3 := pow_nonneg hd.le 3
  unfold surplusKernel
  rw [abs_le]; constructor <;> nlinarith

/-! ### The first-order correction for a quartic gauge -/

/-- `h(x) − a₀` for the quartic gauge. -/
def quarticSlope (a₁ a₂ a₃ a₄ x : ℝ) : ℝ := a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4

/-- An antiderivative of `y (H − a₁ y − a₂ y² − a₃ y³ − a₄ y⁴)`. -/
def firstMomentAnti (a₁ a₂ a₃ a₄ H y : ℝ) : ℝ :=
  H * y ^ 2 / 2 - a₁ * y ^ 3 / 3 - a₂ * y ^ 4 / 4 - a₃ * y ^ 5 / 5 - a₄ * y ^ 6 / 6

/-- An antiderivative of `H − a₁ y − a₂ y² − a₃ y³ − a₄ y⁴`. -/
def zerothMomentAnti (a₁ a₂ a₃ a₄ H y : ℝ) : ℝ :=
  H * y - a₁ * y ^ 2 / 2 - a₂ * y ^ 3 / 3 - a₃ * y ^ 4 / 4 - a₄ * y ^ 5 / 5

/-- The first-order surplus of a quartic gauge:
`∫_0^r (min(x, y)/24 + xy/8)(h(x) − h(y)) dy`, as an explicit polynomial in `x` and `r`. -/
def firstOrderSurplus (a₁ a₂ a₃ a₄ r x : ℝ) : ℝ :=
  (1 / 24 + x / 8) * firstMomentAnti a₁ a₂ a₃ a₄ (quarticSlope a₁ a₂ a₃ a₄ x) x +
    x / 24 * (zerothMomentAnti a₁ a₂ a₃ a₄ (quarticSlope a₁ a₂ a₃ a₄ x) r -
      zerothMomentAnti a₁ a₂ a₃ a₄ (quarticSlope a₁ a₂ a₃ a₄ x) x) +
    x / 8 * (firstMomentAnti a₁ a₂ a₃ a₄ (quarticSlope a₁ a₂ a₃ a₄ x) r -
      firstMomentAnti a₁ a₂ a₃ a₄ (quarticSlope a₁ a₂ a₃ a₄ x) x)

theorem hasDerivAt_firstMomentAnti (a₁ a₂ a₃ a₄ H y : ℝ) :
    HasDerivAt (firstMomentAnti a₁ a₂ a₃ a₄ H)
      (y * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4)) y := by
  have h := (((((((hasDerivAt_pow 2 y).const_mul H).div_const 2).sub
    (((hasDerivAt_pow 3 y).const_mul a₁).div_const 3)).sub
    (((hasDerivAt_pow 4 y).const_mul a₂).div_const 4)).sub
    (((hasDerivAt_pow 5 y).const_mul a₃).div_const 5)).sub
    (((hasDerivAt_pow 6 y).const_mul a₄).div_const 6))
  exact h.congr_deriv (by norm_num; ring)

theorem hasDerivAt_zerothMomentAnti (a₁ a₂ a₃ a₄ H y : ℝ) :
    HasDerivAt (zerothMomentAnti a₁ a₂ a₃ a₄ H)
      (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4) y := by
  have h := ((((((hasDerivAt_id' y).const_mul H).sub
    (((hasDerivAt_pow 2 y).const_mul a₁).div_const 2)).sub
    (((hasDerivAt_pow 3 y).const_mul a₂).div_const 3)).sub
    (((hasDerivAt_pow 4 y).const_mul a₃).div_const 4)).sub
    (((hasDerivAt_pow 5 y).const_mul a₄).div_const 5))
  exact h.congr_deriv (by norm_num; ring)

/-- **The first-order surplus integral.** For `0 < x ≤ r`,
`∫_0^r ((x + y − |x − y|)/48 + xy/8)(h(x) − h(y)) dy = firstOrderSurplus`. -/
theorem integral_firstOrder_quarticGauge (a₀ a₁ a₂ a₃ a₄ : ℝ) {r x : ℝ} (hx : 0 < x) (hxr : x ≤ r) :
    IntegrableOn (fun y => ((x + y - |x - y|) / 48 + x * y / 8) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) (Ioc 0 r) ∧
      (∫ y in Ioc 0 r, ((x + y - |x - y|) / 48 + x * y / 8) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) =
      firstOrderSurplus a₁ a₂ a₃ a₄ r x := by
  set H := quarticSlope a₁ a₂ a₃ a₄ x with hH
  have hc : Continuous fun y => ((x + y - |x - y|) / 48 + x * y / 8) *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) := by
    unfold quarticGauge; fun_prop
  refine ⟨hc.integrableOn_Ioc, ?_⟩
  have hdiff : ∀ y, quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y =
      H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4 := fun y => by
    rw [hH]; unfold quarticGauge quarticSlope; ring
  rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr, setIntegral_union (Set.disjoint_left.mpr fun y h1 h2 => by
    linarith [h1.2, h2.1]) measurableSet_Ioc hc.integrableOn_Ioc hc.integrableOn_Ioc,
    ← intervalIntegral.integral_of_le hx.le, ← intervalIntegral.integral_of_le hxr]
  -- below `x`: `min(x, y) = y`
  have h1 : (∫ y in (0 : ℝ)..x, ((x + y - |x - y|) / 48 + x * y / 8) *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) =
      (1 / 24 + x / 8) * firstMomentAnti a₁ a₂ a₃ a₄ H x := by
    have e : EqOn (fun y => ((x + y - |x - y|) / 48 + x * y / 8) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y))
        (fun y => (1 / 24 + x / 8) * (y * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4)))
        (uIcc 0 x) := fun y hy => by
      rw [uIcc_of_le hx.le] at hy
      simp only
      rw [abs_of_nonneg (by linarith [hy.2] : 0 ≤ x - y), hdiff]; ring
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_firstMomentAnti a₁ a₂ a₃ a₄ H y)
        ((by fun_prop : Continuous fun y : ℝ =>
          y * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4)).intervalIntegrable _ _)]
    unfold firstMomentAnti; ring
  -- above `x`: `min(x, y) = x`
  have h2 : (∫ y in x..r, ((x + y - |x - y|) / 48 + x * y / 8) *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) =
      x / 24 * (zerothMomentAnti a₁ a₂ a₃ a₄ H r - zerothMomentAnti a₁ a₂ a₃ a₄ H x) +
        x / 8 * (firstMomentAnti a₁ a₂ a₃ a₄ H r - firstMomentAnti a₁ a₂ a₃ a₄ H x) := by
    have e : EqOn (fun y => ((x + y - |x - y|) / 48 + x * y / 8) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y))
        (fun y => x / 24 * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4) +
          x / 8 * (y * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4))) (uIcc x r) :=
      fun y hy => by
        rw [uIcc_of_le hxr] at hy
        simp only
        rw [abs_of_nonpos (by linarith [hy.1] : x - y ≤ 0), hdiff]; ring
    have i0 : IntervalIntegrable (fun y : ℝ => x / 24 * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 -
        a₄ * y ^ 4)) volume x r := (by fun_prop : Continuous fun y : ℝ =>
          x / 24 * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4)).intervalIntegrable _ _
    have i1 : IntervalIntegrable (fun y : ℝ => x / 8 * (y * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 -
        a₄ * y ^ 4))) volume x r := (by fun_prop : Continuous fun y : ℝ =>
          x / 8 * (y * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4))).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_add i0 i1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => hasDerivAt_zerothMomentAnti a₁ a₂ a₃ a₄ H y)
        ((by fun_prop : Continuous fun y : ℝ =>
          H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4).intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => hasDerivAt_firstMomentAnti a₁ a₂ a₃ a₄ H y)
        ((by fun_prop : Continuous fun y : ℝ =>
          y * (H - a₁ * y - a₂ * y ^ 2 - a₃ * y ^ 3 - a₄ * y ^ 4)).intervalIntegrable _ _)]
  rw [h1, h2]
  unfold firstOrderSurplus
  rw [← hH]
  ring

/-! ### The surplus potential of a quartic gauge to second order -/

/-- **The quartic surplus potential to second order.** For a quartic gauge `h`, `L`-Lipschitz on
`[0, r]`, `r ≤ 3/8`: `h(x) U_h(x) ≥ quarticSurplusMain + firstOrderSurplus − L (4/125) r⁵`. -/
theorem mul_surplusPotential_quarticGauge_ge_second (a₀ a₁ a₂ a₃ a₄ : ℝ) {r x L : ℝ} (hx : 0 < x)
    (hxr : x ≤ r) (hr : r ≤ 3 / 8) (hhx : 0 < quarticGauge a₀ a₁ a₂ a₃ a₄ x)
    (hL : ∀ u v, 0 ≤ u → u ≤ r → 0 ≤ v → v ≤ r →
      |a₁ + a₂ * (u + v) + a₃ * (u ^ 2 + u * v + v ^ 2) +
        a₄ * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)| ≤ L) :
    quarticSurplusMain a₁ a₂ a₃ a₄ r x + firstOrderSurplus a₁ a₂ a₃ a₄ r x - L * (4 / 125 * r ^ 5) ≤
      quarticGauge a₀ a₁ a₂ a₃ a₄ x * surplusPotential (quarticGauge a₀ a₁ a₂ a₃ a₄) r x := by
  have hlip : ∀ y, 0 ≤ y → y ≤ r →
      |quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y| ≤ L * |x - y| :=
    fun y hy0 hyr => by
      rw [quarticGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hL x y hx.le hxr hy0 hyr) (abs_nonneg _)
  obtain ⟨hP, hPeq⟩ := integral_principalSurplus_quarticGauge a₀ a₁ a₂ a₃ a₄ hx hxr
  obtain ⟨hT, hTeq⟩ := integral_firstOrder_quarticGauge a₀ a₁ a₂ a₃ a₄ hx hxr
  have hU : quarticGauge a₀ a₁ a₂ a₃ a₄ x * surplusPotential (quarticGauge a₀ a₁ a₂ a₃ a₄) r x =
      ∫ y in Ioc 0 r, surplusKernel x y *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) := by
    unfold surplusPotential
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    have e : quarticGauge a₀ a₁ a₂ a₃ a₄ x *
        (1 - quarticGauge a₀ a₁ a₂ a₃ a₄ y / quarticGauge a₀ a₁ a₂ a₃ a₄ x) =
        quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y := by
      field_simp
    calc quarticGauge a₀ a₁ a₂ a₃ a₄ x * (surplusKernel x y *
          (1 - quarticGauge a₀ a₁ a₂ a₃ a₄ y / quarticGauge a₀ a₁ a₂ a₃ a₄ x)) =
        surplusKernel x y * (quarticGauge a₀ a₁ a₂ a₃ a₄ x *
          (1 - quarticGauge a₀ a₁ a₂ a₃ a₄ y / quarticGauge a₀ a₁ a₂ a₃ a₄ x)) := by ring
      _ = _ := by rw [e]
  have hmk : Measurable fun y => surplusKernel x y := measurable_surplusKernel.of_uncurry_left
  have hmh : Measurable fun y => quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y :=
    measurable_const.sub (continuous_quarticGauge a₀ a₁ a₂ a₃ a₄).measurable
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL 0 0 le_rfl (by linarith) le_rfl (by linarith))
  have hK : IntegrableOn (fun y => surplusKernel x y *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) (Ioc 0 r) := by
    refine Measure.integrableOn_of_bounded (M := 3 / 2 * L) (by simp)
      (hmk.mul hmh).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    by_cases hxy : x = y
    · rw [hxy, sub_self, mul_zero, abs_zero]; positivity
    have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hk0 := surplusKernel_nonneg hx hy.1 hxy
    have hk1 := (surplusKernel_le hx hy.1).trans (archLevyDensity_le_of_le_one hd
      (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]))
    rw [abs_mul, abs_of_nonneg hk0]
    calc surplusKernel x y * |quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y| ≤
          3 / 2 / |x - y| * (L * |x - y|) :=
          mul_le_mul hk1 (hlip y hy.1.le hy.2) (abs_nonneg _) (by positivity)
      _ = 3 / 2 * L := by field_simp
  have hpt : ∀ y ∈ Ioc 0 r, (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) +
      ((x + y - |x - y|) / 48 + x * y / 8) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) - L * (4 / 125 * r ^ 4) ≤
        surplusKernel x y * (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) := by
    intro y hy
    have hr0 : 0 ≤ r := by linarith
    by_cases hxy : x = y
    · rw [hxy]
      simp only [sub_self, mul_zero, add_zero]
      have : 0 ≤ L * (4 / 125 * r ^ 4) := by positivity
      linarith
    set E := surplusKernel x y - (1 / (2 * |x - y|) - 1 / (2 * (x + y))) -
      ((x + y - |x - y|) / 48 + x * y / 8) with hE
    set D := quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y with hD
    have hdiff : |E| ≤ (x + y) ^ 3 / 250 :=
      abs_surplusKernel_sub_secondOrder_le hx hy.1 hxy (by linarith [hy.2])
    have hs3 : (x + y) ^ 3 ≤ (2 * r) ^ 3 :=
      pow_le_pow_left₀ (by linarith [hy.1]) (by linarith [hy.2]) 3
    have hl : |D| ≤ L * r := by
      refine (hlip y hy.1.le hy.2).trans (mul_le_mul_of_nonneg_left ?_ hL0)
      rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have hprod : |E| * |D| ≤ (2 * r) ^ 3 / 250 * (L * r) :=
      mul_le_mul (hdiff.trans (by linarith)) hl (abs_nonneg _) (by positivity)
    have hlow := neg_abs_le (E * D)
    rw [abs_mul] at hlow
    have e : surplusKernel x y * D = (1 / (2 * |x - y|) - 1 / (2 * (x + y))) * D +
        ((x + y - |x - y|) / 48 + x * y / 8) * D + E * D := by rw [hE]; ring
    have e2 : (2 * r) ^ 3 / 250 * (L * r) = L * (4 / 125 * r ^ 4) := by ring
    rw [e]
    linarith
  have hconst : IntegrableOn (fun _ : ℝ => L * (4 / 125 * r ^ 4)) (Ioc 0 r) := by
    exact integrableOn_const (by simp)
  have hPT : IntegrableOn (fun y => (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) +
      ((x + y - |x - y|) / 48 + x * y / 8) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) (Ioc 0 r) := hP.add hT
  have hPE : IntegrableOn (fun y => (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) +
      ((x + y - |x - y|) / 48 + x * y / 8) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) -
      L * (4 / 125 * r ^ 4)) (Ioc 0 r) := hPT.sub hconst
  have hmono := setIntegral_mono_on hPE hK measurableSet_Ioc hpt
  rw [MeasureTheory.integral_sub hPT hconst, MeasureTheory.integral_add hP hT, hPeq, hTeq,
    setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul] at hmono
  rw [hU]
  have e3 : (r - 0) * (L * (4 / 125 * r ^ 4)) = L * (4 / 125 * r ^ 5) := by ring
  linarith

/-! ### The antiderivative to second order -/

private theorem arctan_le_self_secondOrder {w : ℝ} (hw : 0 ≤ w) : Real.arctan w ≤ w := by
  have h := integral_one_div_one_add_sq (a := 0) (b := w)
  rw [Real.arctan_zero, sub_zero] at h
  rw [← h]
  have hle : ∫ t in (0 : ℝ)..w, 1 / (1 + t ^ 2) ≤ ∫ _t in (0 : ℝ)..w, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on hw ?_ intervalIntegrable_const fun t _ => ?_
    · exact (continuous_const.div (continuous_const.add (continuous_pow 2))
        fun t => (by positivity : (0 : ℝ) < 1 + t ^ 2).ne').intervalIntegrable _ _
    · rw [div_le_one (by positivity)]; nlinarith [sq_nonneg t]
  simpa using hle

/-- `tanh z ≤ z − z³/3 + z⁵/5` on `[0, 1/4]`. -/
theorem tanh_le_quintic {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 4) :
    Real.tanh z ≤ z - z ^ 3 / 3 + z ^ 5 / 5 := by
  have hz : |z| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hzn : |-z| ≤ 1 := by rwa [abs_neg]
  have hp := exp_le_taylor_six hz
  have hm := taylor_six_le_exp hzn
  rw [abs_of_nonneg h0] at hp
  rw [abs_neg, abs_of_nonneg h0] at hm
  have hS : Real.sinh z ≤ z + z ^ 3 / 6 + z ^ 5 / 120 + z ^ 6 / 617 := by
    rw [Real.sinh_eq]; linarith
  have hc := cosh_ge_taylor_four h0 (by linarith)
  have hC : 0 < Real.cosh z := Real.cosh_pos z
  have hq : 0 ≤ z - z ^ 3 / 3 + z ^ 5 / 5 := by nlinarith [pow_nonneg h0 5]
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ hC]
  have hprod := mul_le_mul_of_nonneg_left hc hq
  -- `(z − z³/3 + z⁵/5)(1 + z²/2 + z⁴/24 − z⁶/300) ≥ z + z³/6 + z⁵/120 + z⁶/617`
  have hpoly : z + z ^ 3 / 6 + z ^ 5 / 120 + z ^ 6 / 617 ≤
      (z - z ^ 3 / 3 + z ^ 5 / 5) * (1 + z ^ 2 / 2 + z ^ 4 / 24 - z ^ 6 / 300) := by
    have h5 : 0 ≤ z ^ 5 := pow_nonneg h0 5
    have hz2 : z ^ 2 ≤ 1 / 16 := by nlinarith
    have hz6 : z ^ 6 ≤ z ^ 5 / 4 := by
      have := mul_le_mul_of_nonneg_left h1 h5; nlinarith
    have hz7 : z ^ 7 ≤ z ^ 5 / 16 := by
      have := mul_le_mul_of_nonneg_left hz2 h5; nlinarith
    have hz9 : z ^ 9 ≤ z ^ 5 / 256 := by
      have h4 : z ^ 4 ≤ 1 / 256 := by nlinarith
      have := mul_le_mul_of_nonneg_left h4 h5; nlinarith
    have hz11 : 0 ≤ z ^ 11 := pow_nonneg h0 11
    have hz9' : 0 ≤ z ^ 9 := pow_nonneg h0 9
    have hz11' : z ^ 11 ≤ z ^ 5 / 4096 := by
      have h6 : z ^ 6 ≤ 1 / 4096 := by nlinarith
      have := mul_le_mul_of_nonneg_left h6 h5; nlinarith
    nlinarith
  linarith

/-- **The antiderivative to second order.** `Ω(y) ≥ −½ log(y/4) + π/4 − y/4 + y²/96` on `(0, 1]`. -/
theorem archLevyAntideriv_ge_second {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    -(1 / 2) * Real.log (y / 4) + Real.pi / 4 - y / 4 + y ^ 2 / 96 ≤ archLevyAntideriv y := by
  set z := y / 4 with hzdef
  have hz : 0 < z := by positivity
  have hz1 : z ≤ 1 / 4 := by rw [hzdef]; linarith
  have hy2 : -y / 2 = -2 * z := by rw [hzdef]; ring
  rw [archLevyAntideriv_eq_log_div hy, hy2, one_add_exp_div_one_sub_exp hz]
  have hs : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hc : 0 < Real.cosh z := Real.cosh_pos z
  obtain ⟨-, hs2, hc1, -⟩ := sinh_cosh_taylor_bounds hz.le (by linarith)
  -- `log(cosh z / sinh z) ≥ −log z + z²/3 − 7z⁴/36`
  set w := z ^ 2 / 3 - z ^ 4 / 12 with hw
  have hw0 : 0 ≤ w := by rw [hw]; nlinarith [pow_nonneg hz.le 4]
  have hratio : 1 + w ≤ z * Real.cosh z / Real.sinh z := by
    rw [le_div_iff₀ hs, hw]
    have h6 : 0 ≤ 1 - z ^ 2 / 6 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc1 hz.le, mul_le_mul hc1 hs2 (by positivity) hc.le]
  have hlog1 : w - w ^ 2 ≤ Real.log (1 + w) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + w by positivity)
    have e : w - w ^ 2 ≤ 1 - (1 + w)⁻¹ := by
      rw [show 1 - (1 + w)⁻¹ = w / (1 + w) by field_simp; ring, le_div_iff₀ (by positivity)]
      nlinarith [pow_nonneg hw0 3]
    linarith
  have hlog2 : Real.log (1 + w) ≤ Real.log (z * Real.cosh z / Real.sinh z) :=
    Real.log_le_log (by positivity) hratio
  have hsplit : Real.log (z * Real.cosh z / Real.sinh z) =
      Real.log z + Real.log (Real.cosh z / Real.sinh z) := by
    rw [mul_div_assoc, Real.log_mul hz.ne' (by positivity)]
  have hww : w - w ^ 2 ≥ z ^ 2 / 3 - 7 * z ^ 4 / 36 := by
    rw [hw]
    have h2 : (z ^ 2 / 3 - z ^ 4 / 12) ^ 2 ≤ z ^ 4 / 9 := by
      have ha : 0 ≤ z ^ 2 / 3 - z ^ 4 / 12 := by rw [← hw]; exact hw0
      have hb : z ^ 2 / 3 - z ^ 4 / 12 ≤ z ^ 2 / 3 := by nlinarith [pow_nonneg hz.le 4]
      nlinarith
    nlinarith
  -- the arctangent
  have hat := arctan_exp_add_arctan_tanh hz.le
  have htanh := tanh_le_quintic hz.le hz1
  have htanh0 : 0 ≤ Real.tanh z := by rw [Real.tanh_eq_sinh_div_cosh]; positivity
  have harc := arctan_le_self_secondOrder htanh0
  have hpoly : 0 ≤ z ^ 3 / 3 - 7 * z ^ 4 / 72 - z ^ 5 / 5 := by
    nlinarith [pow_nonneg hz.le 3, mul_nonneg (pow_nonneg hz.le 3) (by linarith : (0 : ℝ) ≤ 1 / 4 - z),
      mul_nonneg (pow_nonneg hz.le 4) (by linarith : (0 : ℝ) ≤ 1 / 4 - z)]
  linarith

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
