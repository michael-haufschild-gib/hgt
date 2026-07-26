import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Rectangular half-density source for Deninger weight one

This module formalizes the tangent-level geometric atom behind a weight-one Deninger flow.
For rectangular modulus `r > 0`, the plane complex structure and normalized metric are

`J_r(x,y) = (-r y, x/r)`,

`g_r((x,y),(x',y')) = x x'/r + r y y'`.

The moving-modulus map `A_q(x,y) = (q x,y)` is complex linear from modulus `r` to modulus
`q r`, scales both metric and oriented area by exactly `q`, and composes multiplicatively.
Thus the moving rectangular family has weight one; on a fixed rectangular fibre the same
coordinate dilation would instead have weight two.

The final rigidity theorem shows that the coefficient `1/r` is forced, up to a constant, by
the continuous positive scaling law.  No Xi divisor, zero location, or RH premise occurs.
-/

namespace RHTower

/-- Complex structure of the rectangular plane with modulus parameter `r`. -/
def deningerRectangularJ (r : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (-r * v.2, v.1 / r)

/-- Positive rectangular metric normalized by the inverse modulus. -/
def deningerRectangularMetric (r : ℝ) (v w : ℝ × ℝ) : ℝ :=
  v.1 * w.1 / r + r * v.2 * w.2

/-- Moving-modulus dilation.  It sends modulus `r` to modulus `q * r`. -/
def deningerRectangularScale (q : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (q * v.1, v.2)

/-- Standard oriented area form in rectangular coordinates. -/
def deningerRectangularArea (v w : ℝ × ℝ) : ℝ :=
  v.1 * w.2 - v.2 * w.1

/-- The rectangular endomorphism is a genuine complex structure. -/
@[simp]
theorem deningerRectangularJ_sq {r : ℝ} (hr : r ≠ 0) (v : ℝ × ℝ) :
    deningerRectangularJ r (deningerRectangularJ r v) = -v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [deningerRectangularJ, hr]

/-- Moving the modulus makes the dilation complex linear. -/
theorem deningerRectangularScale_intertwines_J
    {q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0) (v : ℝ × ℝ) :
    deningerRectangularScale q (deningerRectangularJ r v) =
      deningerRectangularJ (q * r) (deningerRectangularScale q v) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [deningerRectangularScale, deningerRectangularJ, hq, hr]
  field_simp

/-- The normalized rectangular form is positive definite for positive modulus. -/
theorem deningerRectangularMetric_self_pos
    {r : ℝ} (hr : 0 < r) {v : ℝ × ℝ} (hv : v ≠ 0) :
    0 < deningerRectangularMetric r v v := by
  rcases v with ⟨x, y⟩
  simp only [Prod.mk_eq_zero] at hv
  simp only [deningerRectangularMetric]
  by_cases hx : x = 0
  · subst x
    simp only [zero_mul, zero_div, zero_add]
    have hy : y ≠ 0 := fun h => hv ⟨rfl, h⟩
    rw [mul_assoc]
    exact mul_pos hr (mul_self_pos.mpr hy)
  · have hxpos : 0 < x * x / r := div_pos (mul_self_pos.mpr hx) hr
    have hy_nonneg : 0 ≤ r * y * y := by positivity
    linarith

/-- Exact weight-one metric law. -/
theorem deningerRectangularMetric_scale
    {q r : ℝ} (hq : q ≠ 0) (hr : r ≠ 0) (v w : ℝ × ℝ) :
    deningerRectangularMetric (q * r)
        (deningerRectangularScale q v) (deningerRectangularScale q w) =
      q * deningerRectangularMetric r v w := by
  rcases v with ⟨x, y⟩
  rcases w with ⟨x', y'⟩
  simp only [deningerRectangularMetric, deningerRectangularScale]
  field_simp
  ring

/-- Exact degree/area law of the moving rectangular dilation. -/
theorem deningerRectangularArea_scale (q : ℝ) (v w : ℝ × ℝ) :
    deningerRectangularArea
        (deningerRectangularScale q v) (deningerRectangularScale q w) =
      q * deningerRectangularArea v w := by
  rcases v with ⟨x, y⟩
  rcases w with ⟨x', y'⟩
  simp only [deningerRectangularArea, deningerRectangularScale]
  ring

/-- Moving-modulus dilations form a multiplicative semigroup. -/
@[simp]
theorem deningerRectangularScale_mul (q₁ q₂ : ℝ) (v : ℝ × ℝ) :
    deningerRectangularScale q₁ (deningerRectangularScale q₂ v) =
      deningerRectangularScale (q₁ * q₂) v := by
  rcases v with ⟨x, y⟩
  simp [deningerRectangularScale, mul_assoc]

/--
Half-density rigidity.  If a scalar metric coefficient has weight one under every positive
moving-modulus dilation, then it is the inverse modulus times one constant.
-/
theorem deningerRectangularCoefficient_eq_const_div
    (c : ℝ → ℝ)
    (hscale : ∀ q r : ℝ, 0 < q → 0 < r →
      c (q * r) * q ^ 2 = q * c r)
    {r : ℝ} (hr : 0 < r) :
    c r = c 1 / r := by
  have h := hscale r 1 hr zero_lt_one
  simp only [mul_one] at h
  apply (eq_div_iff (ne_of_gt hr)).2
  nlinarith

end RHTower
