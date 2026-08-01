import GaloisForLFunctions.RHTower.DeningerArithmeticRectangularQuaternionicHodge
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Leafwise Kähler structure on a complex leaf

On a complex leaf with coordinate `z = u + i v`, one-forms are coefficient pairs `a du + b dv`,
the Kähler form is the wedge coefficient, and the Hodge star is the quarter turn.  The star
squares to `-1`, and every nonzero one-form has strictly positive `α ∧ *α`.

Scaling the leaf coordinate by `s` scales the Kähler form by `s²`; the half-density flow scales
by `e^{t/2}`, so the form scales by `e^t`.  A radial function pulls back along the flow by
rescaling its argument.

* `deningerLeafStar_star` : `*² = -1`.
* `deningerLeafWedge_star_pos` : `α ∧ *α > 0`.
* `deningerLeafWedge_smul` and `deningerLeafFlow_wedge` : the Kähler scaling law.
* `deningerRadialFlowPullback` : the radial pullback law.
-/

namespace RHTower

section LeafwiseKahler

/-- The Kähler coefficient of the wedge of two real leafwise one-forms. -/
def deningerLeafWedge (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1

/-- The leafwise Hodge star: `*du = dv`, `*dv = -du`. -/
def deningerLeafStar (a : ℝ × ℝ) : ℝ × ℝ := (-a.2, a.1)

/-- **The star squares to `-1`.** -/
theorem deningerLeafStar_star (a : ℝ × ℝ) :
    deningerLeafStar (deningerLeafStar a) = -a := by
  rcases a with ⟨x, y⟩
  simp [deningerLeafStar, Prod.neg_mk]

/-- The star sends `du` to `dv`. -/
theorem deningerLeafStar_du : deningerLeafStar (1, 0) = (0, 1) := by
  simp [deningerLeafStar]

/-- The star sends `dv` to `-du`. -/
theorem deningerLeafStar_dv : deningerLeafStar (0, 1) = (-1, 0) := by
  simp [deningerLeafStar]

/-- The wedge against the star is the squared length. -/
theorem deningerLeafWedge_star (a : ℝ × ℝ) :
    deningerLeafWedge a (deningerLeafStar a) = a.1 ^ 2 + a.2 ^ 2 := by
  rcases a with ⟨x, y⟩
  simp only [deningerLeafWedge, deningerLeafStar]
  ring

/-- **Positivity of the leafwise cup--star pairing.** -/
theorem deningerLeafWedge_star_pos {a : ℝ × ℝ} (ha : a ≠ 0) :
    0 < deningerLeafWedge a (deningerLeafStar a) := by
  rw [deningerLeafWedge_star]
  rcases a with ⟨x, y⟩
  have hxy : ¬ (x = 0 ∧ y = 0) := by
    intro h
    exact ha (by rw [h.1, h.2]; rfl)
  rcases not_and_or.mp hxy with hx | hy
  · have : 0 < x ^ 2 := by positivity
    nlinarith [sq_nonneg y]
  · have : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg x]

/-- Scaling both one-forms scales the Kähler coefficient quadratically. -/
theorem deningerLeafWedge_smul (s : ℝ) (a b : ℝ × ℝ) :
    deningerLeafWedge (s • a) (s • b) = s ^ 2 * deningerLeafWedge a b := by
  rcases a with ⟨x, y⟩
  rcases b with ⟨z, w⟩
  simp only [deningerLeafWedge, Prod.smul_mk, smul_eq_mul]
  ring

/-- **The Kähler scaling law of the half-density flow.**  The flow scales the leaf coordinate by
`e^{t/2}`, so it scales the Kähler form by `e^t`. -/
theorem deningerLeafFlow_wedge (t : ℝ) (a b : ℝ × ℝ) :
    deningerLeafWedge (Real.exp (t / 2) • a) (Real.exp (t / 2) • b)
      = Real.exp t * deningerLeafWedge a b := by
  rw [deningerLeafWedge_smul]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- **The radial pullback law.**  A radial function pulls back along the flow at time `log n` by
rescaling its argument by `n`. -/
theorem deningerRadialFlowPullback (f : ℝ → ℂ) {n : ℝ} (hn : 0 < n) (z : ℂ) :
    f (‖(Real.exp (Real.log n / 2) : ℂ) * z‖ ^ 2) = f (n * ‖z‖ ^ 2) := by
  congr 1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), mul_pow]
  congr 1
  rw [← Real.exp_nat_mul]
  have hhalf : (2 : ℕ) * (Real.log n / 2) = Real.log n := by
    push_cast
    ring
  rw [hhalf, Real.exp_log hn]

end LeafwiseKahler

end RHTower
