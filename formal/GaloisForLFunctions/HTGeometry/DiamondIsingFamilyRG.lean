import GaloisForLFunctions.HTGeometry.DiamondIsingRG

/-!
# Exact branching diamond-Ising renormalization algebra

This module records the unconditional algebra of the zero-field Ising model on every
`b`-branch, two-bond diamond hierarchical lattice.  If `t` is physical transmissivity, the exact
RG step is

`R_b(t) = ((1+t²)^b - (1-t²)^b) / ((1+t²)^b + (1-t²)^b)`.

The results below derive both projective RG weights from the physical equal/unequal-spin weights,
recover the already formalized two-branch map, expose the exact phase-anchor factors, prove the
quadratic high-temperature contact, and rule out cancellation of the primitive numerator and
normalization divisor over `ℂ`.

The external analytic fixed-point and Ritt--Becker--Bergweiler classification theorems are not
encoded as assumptions.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- Exact `b`-branch diamond-Ising RG map in the rational physical transmissivity field. -/
def diamondIsingFamilyRG (b : ℕ) : RatFunc ℚ :=
  ((1 + RatFunc.X ^ 2) ^ b - (1 - RatFunc.X ^ 2) ^ b) /
    ((1 + RatFunc.X ^ 2) ^ b + (1 - RatFunc.X ^ 2) ^ b)

/-- Primitive numerator of the exact `b`-branch transmissivity map. -/
def diamondIsingFamilyNumerator (b : ℕ) : ℚ[X] :=
  (1 + X ^ 2) ^ b - (1 - X ^ 2) ^ b

/-- Primitive block-normalization denominator of the exact `b`-branch map. -/
def diamondIsingFamilyDenominator (b : ℕ) : ℚ[X] :=
  (1 + X ^ 2) ^ b + (1 - X ^ 2) ^ b

/-- The previously formalized two-branch RG map is exactly the `b=2` family member. -/
theorem diamondIsingFamilyRG_two :
    diamondIsingFamilyRG 2 = diamondIsingRG := by
  simp [diamondIsingFamilyRG, diamondIsingRG]
  ring_nf
  rw [show (2 + RatFunc.X ^ 4 * 2 : RatFunc ℚ) = 2 * (1 + RatFunc.X ^ 4) by ring]
  rw [mul_inv]
  norm_num
  ring

/-- Exact equal-endpoint block weight after two-bond series reduction and `b` parallel branches. -/
theorem diamondIsingBlockSameWeight (b : ℕ) (A t : ℚ) :
    (((A * (1 + t)) ^ 2 + (A * (1 - t)) ^ 2) ^ b) =
      (2 * A ^ 2) ^ b * (1 + t ^ 2) ^ b := by
  rw [← mul_pow]
  congr 1
  ring

/-- Exact unequal-endpoint block weight after two-bond series reduction and `b` parallel branches. -/
theorem diamondIsingBlockDifferentWeight (b : ℕ) (A t : ℚ) :
    ((2 * (A * (1 + t)) * (A * (1 - t))) ^ b) =
      (2 * A ^ 2) ^ b * (1 - t ^ 2) ^ b := by
  rw [← mul_pow]
  congr 1
  ring

/-- The projective difference of the physical block weights carries the family numerator. -/
theorem diamondIsingBlockWeightDifference (b : ℕ) (A t : ℚ) :
    (((A * (1 + t)) ^ 2 + (A * (1 - t)) ^ 2) ^ b) -
        ((2 * (A * (1 + t)) * (A * (1 - t))) ^ b) =
      (2 * A ^ 2) ^ b * ((1 + t ^ 2) ^ b - (1 - t ^ 2) ^ b) := by
  rw [diamondIsingBlockSameWeight, diamondIsingBlockDifferentWeight]
  ring

/-- The projective sum of the physical block weights carries the family normalization divisor. -/
theorem diamondIsingBlockWeightSum (b : ℕ) (A t : ℚ) :
    (((A * (1 + t)) ^ 2 + (A * (1 - t)) ^ 2) ^ b) +
        ((2 * (A * (1 + t)) * (A * (1 - t))) ^ b) =
      (2 * A ^ 2) ^ b * ((1 + t ^ 2) ^ b + (1 - t ^ 2) ^ b) := by
  rw [diamondIsingBlockSameWeight, diamondIsingBlockDifferentWeight]
  ring

/-- Exact low-temperature factor: denominator minus numerator is the `b`-fold unequal-spin face. -/
theorem diamondIsingFamily_denominator_sub_numerator (b : ℕ) :
    diamondIsingFamilyDenominator b - diamondIsingFamilyNumerator b =
      2 * (1 - X ^ 2) ^ b := by
  simp [diamondIsingFamilyDenominator, diamondIsingFamilyNumerator]
  ring

/-- Exact high-temperature companion factor. -/
theorem diamondIsingFamily_denominator_add_numerator (b : ℕ) :
    diamondIsingFamilyDenominator b + diamondIsingFamilyNumerator b =
      2 * (1 + X ^ 2) ^ b := by
  simp [diamondIsingFamilyDenominator, diamondIsingFamilyNumerator]
  ring

/-- The high-temperature anchor has zero numerator for every branch count. -/
@[simp] theorem diamondIsingFamilyNumerator_eval_zero (b : ℕ) :
    (diamondIsingFamilyNumerator b).eval 0 = 0 := by
  simp [diamondIsingFamilyNumerator]

/-- The high-temperature normalization stays nonzero for every branch count. -/
@[simp] theorem diamondIsingFamilyDenominator_eval_zero (b : ℕ) :
    (diamondIsingFamilyDenominator b).eval 0 = 2 := by
  simp [diamondIsingFamilyDenominator]
  norm_num

/-- At positive branch count, numerator and denominator agree at the low-temperature anchor. -/
theorem diamondIsingFamilyNumerator_eval_one (b : ℕ) (hb : 0 < b) :
    (diamondIsingFamilyNumerator b).eval 1 = 2 ^ b := by
  norm_num [diamondIsingFamilyNumerator, zero_pow (Nat.ne_of_gt hb)]

/-- At positive branch count, the low-temperature normalization is nonzero and equals `2^b`. -/
theorem diamondIsingFamilyDenominator_eval_one (b : ℕ) (hb : 0 < b) :
    (diamondIsingFamilyDenominator b).eval 1 = 2 ^ b := by
  norm_num [diamondIsingFamilyDenominator, zero_pow (Nat.ne_of_gt hb)]

/-- The family numerator always has at least quadratic contact at the high-temperature anchor. -/
theorem diamondIsingFamilyNumerator_X_sq_dvd (b : ℕ) :
    X ^ 2 ∣ diamondIsingFamilyNumerator b := by
  have h := sub_dvd_pow_sub_pow (1 + X ^ 2 : ℚ[X]) (1 - X ^ 2) b
  rw [show (1 + X ^ 2 : ℚ[X]) - (1 - X ^ 2) = 2 * X ^ 2 by ring] at h
  rcases h with ⟨q, hq⟩
  refine ⟨2 * q, ?_⟩
  change (1 + X ^ 2) ^ b - (1 - X ^ 2) ^ b = X ^ 2 * (2 * q)
  rw [hq]
  ring

/-- Exact second derivative at the high-temperature anchor.  For `b>0` this proves that the
quadratic contact is not of higher order. -/
theorem diamondIsingFamilyNumerator_secondDerivative_eval_zero (b : ℕ) :
    (derivative (derivative (diamondIsingFamilyNumerator b))).eval 0 =
      4 * (b : ℚ) := by
  simp [diamondIsingFamilyNumerator, derivative_pow]
  ring

/-- Primitive numerator and block-normalization denominator have no common complex zero.  This is
the pointwise noncancellation statement behind the exact rational family. -/
theorem diamondIsingFamilyScalar_noCommonZero (b : ℕ) (t : ℂ)
    (hN : (1 + t ^ 2) ^ b - (1 - t ^ 2) ^ b = 0)
    (hD : (1 + t ^ 2) ^ b + (1 - t ^ 2) ^ b = 0) : False := by
  cases b with
  | zero => norm_num at hD
  | succ b =>
      have hplus : (1 + t ^ 2) ^ (b + 1) = 0 := by
        linear_combination (hN + hD) / 2
      have hminus : (1 - t ^ 2) ^ (b + 1) = 0 := by
        linear_combination (hD - hN) / 2
      have hp : (1 + t ^ 2) = 0 :=
        (pow_eq_zero_iff (Nat.succ_ne_zero b)).mp hplus
      have hm : (1 - t ^ 2) = 0 :=
        (pow_eq_zero_iff (Nat.succ_ne_zero b)).mp hminus
      have htwo : (2 : ℂ) = 0 := by
        linear_combination hp + hm
      norm_num at htwo

end


end GaloisForLFunctions.HTGeometry
