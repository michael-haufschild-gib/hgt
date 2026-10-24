import GaloisForLFunctions.HTGeometry.LogConcaveIntegralComposition
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!+# Gaussian integer masses and positive theta kernels

The power-weighted Gaussian integer sum has a positive integral representation
through the actual theta source. The causal kernels in that representation
preserve two-by-two positivity, including the common Gaussian scale shared
by distinct divisibility events.
-/

open MeasureTheory Set Filter Topology

namespace RHTower.GaussianDivisibility

open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

/-- The literal positive-integer Gaussian mass, with a real power weight. -/
def integerGaussianMass (σ y : ℝ) : ℝ :=
  ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-σ)) *
    Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)

/-- The positive second Gaussian moment before normalization. -/
def gaussianSecondMass (y : ℝ) : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2 *
    Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)

theorem summable_integerGaussianMass {σ y : ℝ} (hσ : 0 ≤ σ) (hy : 0 < y) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ)) *
      Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hs : Summable (fun n : ℕ => Real.exp (-y * (n : ℝ) ^ 2)) := by
    simpa only [pow_zero, one_mul] using summable_pow_mul_exp_neg_nat_sq 0 hy
  apply Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hs)
  intro n
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hn (neg_nonpos.mpr hσ)
  rw [Real.norm_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (zero_le_one.trans hn) _) (Real.exp_pos _).le)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le

theorem summable_gaussianSecondMass {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (-y * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
  (summable_nat_add_iff 1).mpr (summable_pow_mul_exp_neg_nat_sq 2 hy)

/-- The native logarithmic theta tail is the unweighted literal Gaussian mass. -/
theorem tail_zero_eq_integerGaussianMass (t : ℝ) :
    thetaCuspTailDerivative 0 t =
      Real.exp (t / 2) * integerGaussianMass 0 (Real.pi * Real.exp (2 * t)) := by
  rw [integerGaussianMass, ← tsum_mul_left, thetaCuspTailDerivative]
  apply tsum_congr
  intro n
  have he : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [thetaCuspTailDerivativePolynomial, thetaCuspPolynomialAtom,
    Polynomial.eval_one, neg_zero, Real.rpow_zero, one_mul, mul_one, he, mul_pow]
  congr 2
  ring

/-- A causal exponential times a nonnegative power of the exponential increment. -/
def causalPowerExp (α c x : ℝ) : ℝ :=
  if 0 < x then (Real.exp (2 * x) - 1) ^ α * Real.exp (c * x) else 0

theorem theta_source_four_point : LogFourPoint thetaCuspFullSource :=
  logFourPoint_of_concaveOn_log thetaCuspFullSource_pos_all
    strictConcaveOn_thetaCuspLogSource.concaveOn

theorem causalPowerExp_nonneg (α c x : ℝ) : 0 ≤ causalPowerExp α c x := by
  unfold causalPowerExp
  split_ifs with hx
  · have hb : 0 ≤ Real.exp (2 * x) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by linarith))
    exact mul_nonneg (Real.rpow_nonneg hb _) (Real.exp_pos _).le
  · exact le_rfl

/-- Exponential increments have an exact positive four-point difference. -/
theorem exp_increment_four_point (x : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.exp (2 * x) - 1) * (Real.exp (2 * (x + a + b)) - 1) ≤
      (Real.exp (2 * (x + a)) - 1) * (Real.exp (2 * (x + b)) - 1) := by
  have hdiff :
      (Real.exp (2 * (x + a)) - 1) * (Real.exp (2 * (x + b)) - 1) -
        (Real.exp (2 * x) - 1) * (Real.exp (2 * (x + a + b)) - 1) =
      Real.exp (2 * x) * (Real.exp (2 * a) - 1) * (Real.exp (2 * b) - 1) := by
    simp only [mul_add, Real.exp_add]
    ring
  have hnonneg := mul_nonneg
    (mul_nonneg (Real.exp_pos (2 * x)).le
      (sub_nonneg.mpr (Real.one_le_exp (by linarith : 0 ≤ 2 * a))))
    (sub_nonneg.mpr (Real.one_le_exp (by linarith : 0 ≤ 2 * b)))
  linarith only [hdiff, hnonneg]

/-- Every nonnegative power preserves the causal kernel's four-point inequality. -/
theorem causalPowerExp_four_point {α : ℝ} (hα : 0 ≤ α) (c : ℝ) :
    LogFourPoint (causalPowerExp α c) := by
  intro x a b ha hb
  by_cases hx : 0 < x
  · have hxa : 0 < x + a := by linarith
    have hxb : 0 < x + b := by linarith
    have hxab : 0 < x + a + b := by linarith
    have hbase (z : ℝ) (hz : 0 < z) : 0 ≤ Real.exp (2 * z) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by linarith))
    have hp := Real.rpow_le_rpow
      (mul_nonneg (hbase x hx) (hbase (x + a + b) hxab))
      (exp_increment_four_point x ha hb) hα
    rw [Real.mul_rpow (hbase x hx) (hbase (x + a + b) hxab),
      Real.mul_rpow (hbase (x + a) hxa) (hbase (x + b) hxb)] at hp
    have he : Real.exp (c * x) * Real.exp (c * (x + a + b)) =
        Real.exp (c * (x + a)) * Real.exp (c * (x + b)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    simp only [causalPowerExp, if_pos hx, if_pos hxa, if_pos hxb, if_pos hxab]
    calc
      _ = ((Real.exp (2 * x) - 1) ^ α * (Real.exp (2 * (x + a + b)) - 1) ^ α) *
          (Real.exp (c * x) * Real.exp (c * (x + a + b))) := by ring
      _ ≤ ((Real.exp (2 * (x + a)) - 1) ^ α *
          (Real.exp (2 * (x + b)) - 1) ^ α) *
          (Real.exp (c * x) * Real.exp (c * (x + a + b))) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by rw [he]; ring
  · rw [causalPowerExp, if_neg hx, zero_mul]
    exact mul_nonneg (causalPowerExp_nonneg α c (x + a))
      (causalPowerExp_nonneg α c (x + b))

end

end RHTower.GaussianDivisibility
