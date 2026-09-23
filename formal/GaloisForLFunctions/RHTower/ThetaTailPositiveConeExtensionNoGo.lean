import GaloisForLFunctions.RHTower.ThetaTailKernelGeometricDeficitSplit

/-!
# Positive-cone data do not control the all-plane theta-tail endpoint

The geometric--deficit split is available only when both real nodes are nonnegative.  The
Riemann-hypothesis endpoint, however, is the double Laplace transform over the whole real plane.
This module gives a continuous symmetric countermodel showing that positive-cone
positive-semidefiniteness, simultaneous-reflection invariance, and entrywise nonnegativity do not
determine the mixed-sign blocks.
-/

open Set

namespace RHTower

noncomputable section

/-- Continuous countermodel which is constant on both same-sign quadrants but has a larger
mixed-sign coupling. -/
def thetaTailPositiveConeExtensionNoGoKernel (x t : ℝ) : ℝ :=
  1 + max 0 (-(x * t))

theorem continuous_thetaTailPositiveConeExtensionNoGoKernel :
    Continuous fun p : ℝ × ℝ =>
      thetaTailPositiveConeExtensionNoGoKernel p.1 p.2 := by
  unfold thetaTailPositiveConeExtensionNoGoKernel
  fun_prop

theorem thetaTailPositiveConeExtensionNoGoKernel_comm (x t : ℝ) :
    thetaTailPositiveConeExtensionNoGoKernel x t =
      thetaTailPositiveConeExtensionNoGoKernel t x := by
  unfold thetaTailPositiveConeExtensionNoGoKernel
  congr 2
  ring

theorem thetaTailPositiveConeExtensionNoGoKernel_neg_neg (x t : ℝ) :
    thetaTailPositiveConeExtensionNoGoKernel (-x) (-t) =
      thetaTailPositiveConeExtensionNoGoKernel x t := by
  unfold thetaTailPositiveConeExtensionNoGoKernel
  congr 2
  ring

theorem thetaTailPositiveConeExtensionNoGoKernel_nonneg (x t : ℝ) :
    0 ≤ thetaTailPositiveConeExtensionNoGoKernel x t := by
  unfold thetaTailPositiveConeExtensionNoGoKernel
  linarith [le_max_left 0 (-(x * t))]

/-- On the whole nonnegative cone the countermodel is the rank-one constant kernel. -/
theorem thetaTailPositiveConeExtensionNoGoKernel_eq_one
    {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    thetaTailPositiveConeExtensionNoGoKernel x t = 1 := by
  unfold thetaTailPositiveConeExtensionNoGoKernel
  rw [max_eq_left]
  · ring
  · exact neg_nonpos.mpr (mul_nonneg hx ht)

/-- Hence every finite quadratic form on nonnegative nodes is a square. -/
theorem thetaTailPositiveConeExtensionNoGoKernel_quadraticForm_eq_sq
    {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (a : Fin n → ℝ) :
    (∑ i, ∑ j, a i * a j *
        thetaTailPositiveConeExtensionNoGoKernel (x i) (x j)) =
      (∑ i, a i) ^ (2 : ℕ) := by
  simp_rw [thetaTailPositiveConeExtensionNoGoKernel_eq_one (hx _) (hx _)]
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- But the mixed-sign two-node compression has a negative direction. -/
theorem thetaTailPositiveConeExtensionNoGoKernel_mixedSign_quadraticForm_neg :
    thetaTailPositiveConeExtensionNoGoKernel 1 1 +
        thetaTailPositiveConeExtensionNoGoKernel (-1) (-1) -
          2 * thetaTailPositiveConeExtensionNoGoKernel 1 (-1) < 0 := by
  norm_num [thetaTailPositiveConeExtensionNoGoKernel]

end

end RHTower
