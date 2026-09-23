import GaloisForLFunctions.HTGeometry.DiamondIsingFamilyRG

/-!
# Exact Bethe holographic Ising renormalization algebra

For branching number `p` and edge transmissivity `a`, the exact boundary-field recursion of the
Bethe-lattice Ising holographic RG becomes the rational map

`F_{p,a}(y) = ((1+ay)^p - (1-ay)^p) / ((1+ay)^p + (1-ay)^p)`

in the physical boundary-magnetization coordinate `y = tanh h`.

This module records the unconditional projective algebra: the primitive numerator and block
normalization, their exact sum/difference factors, the fixed-point multiplier anchors, the
nontrivial critical map, the noiseless endpoint anchors, and the absence of numerator-denominator
cancellation over `ℂ`.

The real fixed-point analysis and the Becker--Bergweiler hypertranscendence classification are
external analytic theorems and are not encoded as assumptions here.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- Twice the one-child likelihood of a positive parent spin after a binary symmetric transfer.
The harmless factor two removes the common probabilistic normalization. -/
def binarySymmetricPositiveTransferWeight (a y : ℚ) : ℚ :=
  ((1 + a) * (1 + y) + (1 - a) * (1 - y)) / 2

/-- Twice the corresponding one-child likelihood of a negative parent spin. -/
def binarySymmetricNegativeTransferWeight (a y : ℚ) : ℚ :=
  ((1 - a) * (1 + y) + (1 + a) * (1 - y)) / 2

/-- A binary symmetric channel attenuates child magnetization by its signal eigenvalue. -/
theorem binarySymmetricPositiveTransferWeight_eq (a y : ℚ) :
    binarySymmetricPositiveTransferWeight a y = 1 + a * y := by
  simp [binarySymmetricPositiveTransferWeight]
  ring

/-- The negative-parent likelihood carries the opposite attenuated magnetization. -/
theorem binarySymmetricNegativeTransferWeight_eq (a y : ℚ) :
    binarySymmetricNegativeTransferWeight a y = 1 - a * y := by
  simp [binarySymmetricNegativeTransferWeight]
  ring

/-- Exact homogeneous belief-propagation update from `p` independent identical BSC branches. -/
def binarySymmetricHomogeneousBP (p : ℕ) (a y : ℚ) : ℚ :=
  ((binarySymmetricPositiveTransferWeight a y) ^ p -
      (binarySymmetricNegativeTransferWeight a y) ^ p) /
    ((binarySymmetricPositiveTransferWeight a y) ^ p +
      (binarySymmetricNegativeTransferWeight a y) ^ p)

/-- The exact homogeneous BSC update is the Bethe sum/difference rational family. -/
theorem binarySymmetricHomogeneousBP_eq (p : ℕ) (a y : ℚ) :
    binarySymmetricHomogeneousBP p a y =
      ((1 + a * y) ^ p - (1 - a * y) ^ p) /
        ((1 + a * y) ^ p + (1 - a * y) ^ p) := by
  simp [binarySymmetricHomogeneousBP,
    binarySymmetricPositiveTransferWeight_eq,
    binarySymmetricNegativeTransferWeight_eq]

/-- Exact `p`-branch Bethe holographic Ising RG map at edge transmissivity `a`. -/
def betheHolographicIsingRG (p : ℕ) (a : ℚ) : RatFunc ℚ :=
  ((1 + (a : RatFunc ℚ) * RatFunc.X) ^ p -
      (1 - (a : RatFunc ℚ) * RatFunc.X) ^ p) /
    ((1 + (a : RatFunc ℚ) * RatFunc.X) ^ p +
      (1 - (a : RatFunc ℚ) * RatFunc.X) ^ p)

/-- Primitive numerator of the exact boundary-magnetization recursion. -/
def betheHolographicIsingNumerator (p : ℕ) (a : ℚ) : ℚ[X] :=
  (1 + C a * X) ^ p - (1 - C a * X) ^ p

/-- Exact descendant block-normalization polynomial. -/
def betheHolographicIsingDenominator (p : ℕ) (a : ℚ) : ℚ[X] :=
  (1 + C a * X) ^ p + (1 - C a * X) ^ p

/-- The projective normalization minus the numerator is the negative boundary-weight face. -/
theorem betheHolographicIsing_denominator_sub_numerator (p : ℕ) (a : ℚ) :
    betheHolographicIsingDenominator p a - betheHolographicIsingNumerator p a =
      2 * (1 - C a * X) ^ p := by
  simp [betheHolographicIsingDenominator, betheHolographicIsingNumerator]
  ring

/-- The projective normalization plus the numerator is the positive boundary-weight face. -/
theorem betheHolographicIsing_denominator_add_numerator (p : ℕ) (a : ℚ) :
    betheHolographicIsingDenominator p a + betheHolographicIsingNumerator p a =
      2 * (1 + C a * X) ^ p := by
  simp [betheHolographicIsingDenominator, betheHolographicIsingNumerator]
  ring

/-- Zero boundary field is a fixed anchor for every branching number and edge transfer. -/
@[simp] theorem betheHolographicIsingNumerator_eval_zero (p : ℕ) (a : ℚ) :
    (betheHolographicIsingNumerator p a).eval 0 = 0 := by
  simp [betheHolographicIsingNumerator]

/-- The block normalization is nonzero at zero boundary field. -/
@[simp] theorem betheHolographicIsingDenominator_eval_zero (p : ℕ) (a : ℚ) :
    (betheHolographicIsingDenominator p a).eval 0 = 2 := by
  simp [betheHolographicIsingDenominator]
  norm_num

/-- Exact numerator derivative at the zero-field anchor. -/
theorem betheHolographicIsingNumerator_derivative_eval_zero (p : ℕ) (a : ℚ) :
    (derivative (betheHolographicIsingNumerator p a)).eval 0 =
      2 * (p : ℚ) * a := by
  simp [betheHolographicIsingNumerator, derivative_pow]
  ring

/-- The normalization has no linear term at the zero-field anchor. -/
theorem betheHolographicIsingDenominator_derivative_eval_zero (p : ℕ) (a : ℚ) :
    (derivative (betheHolographicIsingDenominator p a)).eval 0 = 0 := by
  simp [betheHolographicIsingDenominator, derivative_pow]

/-- The rational fixed-point multiplier extracted from the primitive projective pair is `p*a`. -/
theorem betheHolographicIsing_linearMultiplier (p : ℕ) (a : ℚ) :
    (derivative (betheHolographicIsingNumerator p a)).eval 0 /
        (betheHolographicIsingDenominator p a).eval 0 =
      (p : ℚ) * a := by
  rw [betheHolographicIsingNumerator_derivative_eval_zero,
    betheHolographicIsingDenominator_eval_zero]
  ring

/-- At the exact Bethe transition `a=1/p`, the zero-field multiplier is one. -/
theorem betheHolographicIsing_critical_linearMultiplier (p : ℕ) (hp : 0 < p) :
    (derivative
          (betheHolographicIsingNumerator p ((p : ℚ)⁻¹))).eval 0 /
        (betheHolographicIsingDenominator p ((p : ℚ)⁻¹)).eval 0 =
      1 := by
  rw [betheHolographicIsing_linearMultiplier]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp))

/-- Cross-multiplied displacement from the identity map. -/
def betheHolographicIsingDisplacementNumerator (p : ℕ) (a : ℚ) : ℚ[X] :=
  betheHolographicIsingNumerator p a -
    X * betheHolographicIsingDenominator p a

/-- At critical transfer, evaluation at the branching value exposes a nonzero displacement. -/
theorem betheHolographicIsing_criticalDisplacement_eval_branching
    (p : ℕ) (hp : 0 < p) :
    (betheHolographicIsingDisplacementNumerator p ((p : ℚ)⁻¹)).eval (p : ℚ) =
      (1 - (p : ℚ)) * 2 ^ p := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hinv : (p : ℚ)⁻¹ * (p : ℚ) = 1 := inv_mul_cancel₀ hpq
  simp [betheHolographicIsingDisplacementNumerator,
    betheHolographicIsingNumerator, betheHolographicIsingDenominator, hinv,
    zero_pow (Nat.ne_of_gt hp)]
  ring

/-- For physical branching `p>=2`, the critical rational RG map is not the identity. -/
theorem betheHolographicIsing_criticalDisplacement_ne_zero
    (p : ℕ) (hp : 2 ≤ p) :
    betheHolographicIsingDisplacementNumerator p ((p : ℚ)⁻¹) ≠ 0 := by
  intro hzero
  have heval := betheHolographicIsing_criticalDisplacement_eval_branching p
    (Nat.zero_lt_of_lt hp)
  rw [hzero] at heval
  simp only [eval_zero] at heval
  have hne : (1 - (p : ℚ)) * 2 ^ p ≠ 0 := by
    apply mul_ne_zero
    · have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp
      linarith
    · positivity
  exact hne heval.symm

/-- Exact cubic critical defect of the cross-multiplied rational map.  Since the primitive
denominator equals two at zero, this is the algebraic anchor for the nonzero cubic term in the
critical expansion of the rational RG map. -/
theorem betheHolographicIsing_criticalDisplacement_thirdDerivative_eval_zero
    (p : ℕ) (hp : 2 ≤ p) :
    (derivative (derivative (derivative
      (betheHolographicIsingDisplacementNumerator p ((p : ℚ)⁻¹))))).eval 0 =
      -4 * (((p : ℚ) ^ (2 : ℕ) - 1) / (p : ℚ) ^ (2 : ℕ)) := by
  simp [betheHolographicIsingDisplacementNumerator,
    betheHolographicIsingNumerator, betheHolographicIsingDenominator,
    derivative_pow]
  have hp1 : 1 ≤ p := by omega
  have hps : 1 ≤ p - 1 := by omega
  norm_num [Nat.cast_sub hp1, Nat.cast_sub hps]
  field_simp [Nat.cast_ne_zero.mpr (by omega : p ≠ 0)]
  ring

/-- At noiseless transfer `a=1`, the positive anchor has equal numerator and normalization. -/
theorem betheHolographicIsingNumerator_eval_one_noiseless (p : ℕ) (hp : 0 < p) :
    (betheHolographicIsingNumerator p 1).eval 1 = 2 ^ p := by
  norm_num [betheHolographicIsingNumerator, zero_pow (Nat.ne_of_gt hp)]

/-- The noiseless positive-anchor normalization is exactly `2^p`. -/
theorem betheHolographicIsingDenominator_eval_one_noiseless (p : ℕ) (hp : 0 < p) :
    (betheHolographicIsingDenominator p 1).eval 1 = 2 ^ p := by
  norm_num [betheHolographicIsingDenominator, zero_pow (Nat.ne_of_gt hp)]

/-- Infinite-temperature transfer collapses the rational recursion to zero. -/
@[simp] theorem betheHolographicIsingRG_zeroTransfer (p : ℕ) :
    betheHolographicIsingRG p 0 = 0 := by
  simp [betheHolographicIsingRG]

/-- The primitive numerator and block normalization have no common complex zero. -/
theorem betheHolographicIsingScalar_noCommonZero (p : ℕ) (a y : ℂ)
    (hN : (1 + a * y) ^ p - (1 - a * y) ^ p = 0)
    (hD : (1 + a * y) ^ p + (1 - a * y) ^ p = 0) : False := by
  cases p with
  | zero => norm_num at hD
  | succ p =>
      have hplus : (1 + a * y) ^ (p + 1) = 0 := by
        linear_combination (hN + hD) / 2
      have hminus : (1 - a * y) ^ (p + 1) = 0 := by
        linear_combination (hD - hN) / 2
      have hp : (1 + a * y) = 0 :=
        (pow_eq_zero_iff (Nat.succ_ne_zero p)).mp hplus
      have hm : (1 - a * y) = 0 :=
        (pow_eq_zero_iff (Nat.succ_ne_zero p)).mp hminus
      have htwo : (2 : ℂ) = 0 := by
        linear_combination hp + hm
      norm_num at htwo

end

end GaloisForLFunctions.HTGeometry
