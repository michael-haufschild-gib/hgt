import GaloisForLFunctions.HTGeometry.BetheHolographicIsingRG

/-!
# Exact asymmetric binary-tree transfer algebra

For a row-stochastic binary channel with

`P(+|+) = α` and `P(+|-) = γ`,

the rescaled one-child likelihood weights of a magnetization message `y` are

`1 + (2α-1)y` and `1 + (2γ-1)y`.

Multiplication of `p` identical independent branch likelihoods gives a two-parameter rational
homogeneous belief-propagation map.  This module formalizes that exact algebra, its symmetric
Bethe-Ising specialization, the zero-message multiplier, projective factors, and primitive
noncancellation over `ℂ`.

The real interval dynamics and the external Becker--Bergweiler hypertranscendence classification
are not encoded as assumptions.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- Twice the one-child likelihood of a positive parent state for channel parameter `α`. -/
def asymmetricBinaryPositiveTransferWeight (α y : ℚ) : ℚ :=
  α * (1 + y) + (1 - α) * (1 - y)

/-- Twice the one-child likelihood of a negative parent state for channel parameter `γ`. -/
def asymmetricBinaryNegativeTransferWeight (γ y : ℚ) : ℚ :=
  γ * (1 + y) + (1 - γ) * (1 - y)

/-- Positive-parent likelihood in the channel's affine signal coordinate. -/
theorem asymmetricBinaryPositiveTransferWeight_eq (α y : ℚ) :
    asymmetricBinaryPositiveTransferWeight α y = 1 + (2 * α - 1) * y := by
  simp [asymmetricBinaryPositiveTransferWeight]
  ring

/-- Negative-parent likelihood in the channel's independent affine signal coordinate. -/
theorem asymmetricBinaryNegativeTransferWeight_eq (γ y : ℚ) :
    asymmetricBinaryNegativeTransferWeight γ y = 1 + (2 * γ - 1) * y := by
  simp [asymmetricBinaryNegativeTransferWeight]
  ring

/-- Exact homogeneous BP update from `p` identical asymmetric-channel branches. -/
def asymmetricBinaryHomogeneousBP (p : ℕ) (α γ y : ℚ) : ℚ :=
  ((asymmetricBinaryPositiveTransferWeight α y) ^ p -
      (asymmetricBinaryNegativeTransferWeight γ y) ^ p) /
    ((asymmetricBinaryPositiveTransferWeight α y) ^ p +
      (asymmetricBinaryNegativeTransferWeight γ y) ^ p)

/-- Exact two-affine-weight form of the asymmetric homogeneous BP update. -/
theorem asymmetricBinaryHomogeneousBP_eq (p : ℕ) (α γ y : ℚ) :
    asymmetricBinaryHomogeneousBP p α γ y =
      ((1 + (2 * α - 1) * y) ^ p - (1 + (2 * γ - 1) * y) ^ p) /
        ((1 + (2 * α - 1) * y) ^ p + (1 + (2 * γ - 1) * y) ^ p) := by
  simp [asymmetricBinaryHomogeneousBP,
    asymmetricBinaryPositiveTransferWeight_eq,
    asymmetricBinaryNegativeTransferWeight_eq]

/-- Exact asymmetric binary-tree rational map in independent affine parameters `u` and `v`. -/
def asymmetricBinaryTreeRG (p : ℕ) (u v : ℚ) : RatFunc ℚ :=
  ((1 + (u : RatFunc ℚ) * RatFunc.X) ^ p -
      (1 + (v : RatFunc ℚ) * RatFunc.X) ^ p) /
    ((1 + (u : RatFunc ℚ) * RatFunc.X) ^ p +
      (1 + (v : RatFunc ℚ) * RatFunc.X) ^ p)

/-- Primitive numerator of the asymmetric binary-tree map. -/
def asymmetricBinaryTreeNumerator (p : ℕ) (u v : ℚ) : ℚ[X] :=
  (1 + C u * X) ^ p - (1 + C v * X) ^ p

/-- Primitive likelihood-normalization denominator of the asymmetric binary-tree map. -/
def asymmetricBinaryTreeDenominator (p : ℕ) (u v : ℚ) : ℚ[X] :=
  (1 + C u * X) ^ p + (1 + C v * X) ^ p

/-- The symmetric slice `v=-u` is exactly the Bethe holographic Ising family. -/
theorem asymmetricBinaryTreeRG_symmetric (p : ℕ) (a : ℚ) :
    asymmetricBinaryTreeRG p a (-a) = betheHolographicIsingRG p a := by
  simp [asymmetricBinaryTreeRG, betheHolographicIsingRG, sub_eq_add_neg]

/-- Normalization minus numerator isolates the negative-parent likelihood face. -/
theorem asymmetricBinaryTree_denominator_sub_numerator (p : ℕ) (u v : ℚ) :
    asymmetricBinaryTreeDenominator p u v - asymmetricBinaryTreeNumerator p u v =
      2 * (1 + C v * X) ^ p := by
  simp [asymmetricBinaryTreeDenominator, asymmetricBinaryTreeNumerator]
  ring

/-- Normalization plus numerator isolates the positive-parent likelihood face. -/
theorem asymmetricBinaryTree_denominator_add_numerator (p : ℕ) (u v : ℚ) :
    asymmetricBinaryTreeDenominator p u v + asymmetricBinaryTreeNumerator p u v =
      2 * (1 + C u * X) ^ p := by
  simp [asymmetricBinaryTreeDenominator, asymmetricBinaryTreeNumerator]
  ring

/-- The uninformative message is a fixed projective anchor. -/
@[simp] theorem asymmetricBinaryTreeNumerator_eval_zero (p : ℕ) (u v : ℚ) :
    (asymmetricBinaryTreeNumerator p u v).eval 0 = 0 := by
  simp [asymmetricBinaryTreeNumerator]

/-- Its exact likelihood normalization is two. -/
@[simp] theorem asymmetricBinaryTreeDenominator_eval_zero (p : ℕ) (u v : ℚ) :
    (asymmetricBinaryTreeDenominator p u v).eval 0 = 2 := by
  simp [asymmetricBinaryTreeDenominator]
  norm_num

/-- Exact primitive numerator derivative at the uninformative message. -/
theorem asymmetricBinaryTreeNumerator_derivative_eval_zero
    (p : ℕ) (u v : ℚ) :
    (derivative (asymmetricBinaryTreeNumerator p u v)).eval 0 =
      (p : ℚ) * (u - v) := by
  simp [asymmetricBinaryTreeNumerator, derivative_pow]
  ring

/-- Exact primitive normalization derivative at the uninformative message. -/
theorem asymmetricBinaryTreeDenominator_derivative_eval_zero
    (p : ℕ) (u v : ℚ) :
    (derivative (asymmetricBinaryTreeDenominator p u v)).eval 0 =
      (p : ℚ) * (u + v) := by
  simp [asymmetricBinaryTreeDenominator, derivative_pow]
  ring

/-- Exact rational fixed-point multiplier `p(u-v)/2`. -/
theorem asymmetricBinaryTree_linearMultiplier (p : ℕ) (u v : ℚ) :
    (derivative (asymmetricBinaryTreeNumerator p u v)).eval 0 /
        (asymmetricBinaryTreeDenominator p u v).eval 0 =
      (p : ℚ) * (u - v) / 2 := by
  rw [asymmetricBinaryTreeNumerator_derivative_eval_zero,
    asymmetricBinaryTreeDenominator_eval_zero]

/-- In stochastic channel parameters, the exact multiplier is `p(α-γ)`. -/
theorem asymmetricBinaryTree_channel_linearMultiplier (p : ℕ) (α γ : ℚ) :
    (derivative
          (asymmetricBinaryTreeNumerator p (2 * α - 1) (2 * γ - 1))).eval 0 /
        (asymmetricBinaryTreeDenominator p (2 * α - 1) (2 * γ - 1)).eval 0 =
      (p : ℚ) * (α - γ) := by
  rw [asymmetricBinaryTree_linearMultiplier]
  ring

/-- Algebraic cross-numerator identity behind strict real monotonicity. -/
theorem asymmetricBinaryTree_derivativeCrossNumerator
    (p : ℕ) (u v : ℚ) :
    derivative (asymmetricBinaryTreeNumerator p u v) *
          asymmetricBinaryTreeDenominator p u v -
        asymmetricBinaryTreeNumerator p u v *
          derivative (asymmetricBinaryTreeDenominator p u v) =
      (2 : ℚ[X]) * (p : ℚ[X]) * (C u - C v) *
        (1 + C u * X) ^ (p - 1) * (1 + C v * X) ^ (p - 1) := by
  cases p with
  | zero =>
      norm_num [asymmetricBinaryTreeNumerator, asymmetricBinaryTreeDenominator]
  | succ p =>
      simp only [asymmetricBinaryTreeNumerator, asymmetricBinaryTreeDenominator,
        derivative_sub, derivative_add, derivative_pow, derivative_one, derivative_mul,
        derivative_C, derivative_X, zero_mul, mul_one, Nat.cast_succ]
      simp only [Nat.succ_sub_one, pow_succ]
      norm_num
      ring

/-- Distinct affine channel parameters prevent any primitive complex cancellation. -/
theorem asymmetricBinaryTreeScalar_noCommonZero
    (p : ℕ) (u v y : ℂ) (huv : u ≠ v)
    (hN : (1 + u * y) ^ p - (1 + v * y) ^ p = 0)
    (hD : (1 + u * y) ^ p + (1 + v * y) ^ p = 0) : False := by
  cases p with
  | zero => norm_num at hD
  | succ p =>
      have hplus : (1 + u * y) ^ (p + 1) = 0 := by
        linear_combination (hN + hD) / 2
      have hminus : (1 + v * y) ^ (p + 1) = 0 := by
        linear_combination (hD - hN) / 2
      have hp : (1 + u * y) = 0 :=
        (pow_eq_zero_iff (Nat.succ_ne_zero p)).mp hplus
      have hm : (1 + v * y) = 0 :=
        (pow_eq_zero_iff (Nat.succ_ne_zero p)).mp hminus
      have huv_y : (u - v) * y = 0 := by
        linear_combination hp - hm
      have hy : y = 0 := (mul_eq_zero.mp huv_y).resolve_left (sub_ne_zero.mpr huv)
      rw [hy] at hp
      norm_num at hp

end

end GaloisForLFunctions.HTGeometry
