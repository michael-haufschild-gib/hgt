import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardCofinalBoundaryLift
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The infinitesimal half-unit seam is an indefinite Cauchy Schur ratio

The unconditional "safe" kernel of the centred logarithmic derivative and the RH kernel differ by
exactly one unit in the Cauchy denominator:

```text
J_safe (x, y) = (Q x + Q y)/(x + y - 1),        J_RH (x, y) = (Q x + Q y)/(x + y),
J_RH = J_safe * H,                              H (x, y) = (x + y - 1)/(x + y).
```

The scalar seam `H` is not positive semidefinite on any two distinct points: its two-point minor is

```text
-(x - y)^2 (2x + 2y - 1) / (4 x y (x + y)^2) < 0 .
```

So no universal scalar Schur multiplier can transport the safe kernel to the RH kernel.  What does
transport it is the *diagonal Fock* covariance `D = J_safe / (x + y)`, the Schur product of the safe
kernel with the Cauchy kernel `1/(x+y) = int_0^infinity e^{-xt} e^{-yt} dt`, and `J_RH = J_safe - D`
exactly.

Also proved here is the pointwise half-plane positivity behind `(2)`: for `Re z > 1/2` and a centred
zero with `|Re lambda| < 1/2`, the Hadamard pair `1/(z - lambda) + 1/(z + lambda)` has strictly
positive real part.
-/

open Complex Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Pointwise positivity of the centred Hadamard pair -/

/-- **Equation (7), termwise.**  Each centred Hadamard pair has positive real part strictly to the
right of the half-unit seam. -/
theorem re_hadamardPair_pos {z lam : ℂ} (hz : 1 / 2 < z.re) (hlam : |lam.re| < 1 / 2) :
    0 < ((z - lam)⁻¹ + (z + lam)⁻¹).re := by
  have h1 : 0 < (z - lam).re := by
    have := abs_lt.1 hlam
    simp only [Complex.sub_re]
    linarith [this.2]
  have h2 : 0 < (z + lam).re := by
    have := abs_lt.1 hlam
    simp only [Complex.add_re]
    linarith [this.1]
  rw [Complex.add_re]
  exact add_pos (_root_.RHTower.re_inv_pos_of_re_pos h1) (_root_.RHTower.re_inv_pos_of_re_pos h2)

/-! ## The three kernels -/

/-- The unconditional safe kernel `(3)`. -/
def safeKernel (Q : ℝ → ℝ) (x y : ℝ) : ℝ := (Q x + Q y) / (x + y - 1)

/-- The RH kernel `(4)`. -/
def rhKernel (Q : ℝ → ℝ) (x y : ℝ) : ℝ := (Q x + Q y) / (x + y)

/-- The scalar seam kernel `(5)`. -/
def seamKernel (x y : ℝ) : ℝ := (x + y - 1) / (x + y)

/-- The diagonal Fock covariance. -/
def fockKernel (Q : ℝ → ℝ) (x y : ℝ) : ℝ := safeKernel Q x y / (x + y)

/-- **Equation (5).**  The RH kernel is the Schur product of the safe kernel with the seam. -/
theorem rhKernel_eq_safe_mul_seam (Q : ℝ → ℝ) {x y : ℝ} (h : x + y - 1 ≠ 0) :
    rhKernel Q x y = safeKernel Q x y * seamKernel x y := by
  unfold rhKernel safeKernel seamKernel
  field_simp

/-- The RH kernel is the safe kernel minus its diagonal Fock covariance. -/
theorem rhKernel_eq_safe_sub_fock (Q : ℝ → ℝ) {x y : ℝ} (h : x + y - 1 ≠ 0) (h' : x + y ≠ 0) :
    rhKernel Q x y = safeKernel Q x y - fockKernel Q x y := by
  unfold rhKernel fockKernel safeKernel
  field_simp

/-- The Cauchy factor of the Fock covariance is the ray Gram matrix `int_0^infinity e^{-(x+y)t}`. -/
theorem integral_exp_ray {x y : ℝ} (h : 0 < x + y) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x * t)) * Real.exp (-(y * t))) = 1 / (x + y) := by
  have hcongr : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x * t)) * Real.exp (-(y * t)))
      = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x + y) * t) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have hval := MeasureTheory.integral_comp_mul_left_Ioi (fun t : ℝ => Real.exp (-t)) 0 h
  simp only [mul_zero, smul_eq_mul] at hval
  rw [hcongr]
  have hcongr2 : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x + y) * t))
      = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-((x + y) * t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 1
    ring
  rw [hcongr2, hval, integral_exp_neg_Ioi_zero, mul_one, one_div]

/-! ## The seam is indefinite -/

/-- **Equation (6).**  The exact two-point seam minor. -/
theorem det_seam_two_point {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : 0 < x + y) :
    seamKernel x x * seamKernel y y - seamKernel x y * seamKernel y x
      = -((x - y) ^ 2 * (2 * x + 2 * y - 1)) / (4 * x * y * (x + y) ^ 2) := by
  unfold seamKernel
  have h2x : (2 : ℝ) * x ≠ 0 := by positivity
  have h2y : (2 : ℝ) * y ≠ 0 := by positivity
  have hs : x + y ≠ 0 := ne_of_gt hxy
  field_simp
  ring

/-- **Equation (6), sign.**  The seam minor is strictly negative at any two distinct points beyond
the half-unit seam. -/
theorem det_seam_two_point_neg {x y : ℝ} (hx : 1 / 2 < x) (hy : 1 / 2 < y) (hne : x ≠ y) :
    seamKernel x x * seamKernel y y - seamKernel x y * seamKernel y x < 0 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hxy : (0 : ℝ) < x + y := by linarith
  rw [det_seam_two_point hx0 hy0 hxy]
  have hnum : 0 < (x - y) ^ 2 * (2 * x + 2 * y - 1) := by
    have h1 : 0 < (x - y) ^ 2 := by positivity
    have h2 : 0 < 2 * x + 2 * y - 1 := by linarith
    positivity
  have hden : 0 < 4 * x * y * (x + y) ^ 2 := by positivity
  rw [neg_div, neg_lt_zero]
  positivity

/-- The two-point seam matrix. -/
def seamMatrix (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![seamKernel x x, seamKernel x y; seamKernel y x, seamKernel y y]

theorem det_seamMatrix (x y : ℝ) :
    (seamMatrix x y).det
      = seamKernel x x * seamKernel y y - seamKernel x y * seamKernel y x := by
  rw [seamMatrix, Matrix.det_fin_two_of]

/-- **The seam kernel is not positive semidefinite.**  Hence no universal scalar Schur multiplier
transports the unconditional safe kernel to the RH kernel. -/
theorem not_posSemidef_seamMatrix {x y : ℝ} (hx : 1 / 2 < x) (hy : 1 / 2 < y) (hne : x ≠ y) :
    ¬ (seamMatrix x y).PosSemidef := by
  intro hpos
  have hdet := hpos.det_nonneg
  rw [det_seamMatrix] at hdet
  exact absurd hdet (not_le.2 (det_seam_two_point_neg hx hy hne))

end GaloisForLFunctions.RHTower

end
