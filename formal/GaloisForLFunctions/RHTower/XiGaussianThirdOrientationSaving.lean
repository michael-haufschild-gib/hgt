import GaloisForLFunctions.RHTower.XiGaussianOrientationPhase

/-!
# A strict source-coefficient saving for the complete third-order phase

At the same-time anchor, factorial recurrence removes the heat parameter
from the ratio of the two envelopes. The adaptive orientation factor then
reduces the third-order source coefficient from `42/41` to below `3/5`,
uniformly over all positive heat times and finite source selections.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiGaussianOrientationOrderFactor (n : ℕ) : ℝ :=
  2 * (n : ℝ) ^ 2 + 2 * (2 * (n : ℝ) + 4) * (2 * (n : ℝ) + 3)

/-- Factorial recurrence gives an exact same-time envelope ratio, without evaluating a
finite list of factorials. -/
theorem xiGaussianOrientationMonomialEnvelope_self (j : ℕ) (t : {t : ℝ // 0 < t}) :
    xiGaussianOrientationMonomialEnvelope j t t = xiGaussianOrientationOrderFactor j *
      (((2 * j + 2).factorial : ℝ) * (2 / (t : ℝ)) ^ (2 * j + 2)) := by
  have hfac (k : ℕ) : ((k + 2).factorial : ℝ) =
      ((k : ℝ) + 2) * ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [show k + 2 = k + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have ht : (t : ℝ) ^ 2 / 2 * (2 / (t : ℝ)) ^ 2 = 2 := by
    field_simp [t.property.ne']
  unfold xiGaussianOrientationMonomialEnvelope xiGaussianOrientationOrderFactor
  rw [show 2 * j + 4 = (2 * j + 2) + 2 by omega, hfac (2 * j + 2),
    pow_add (2 / (t : ℝ)) (2 * j + 2) 2]
  push_cast
  calc
    _ = (2 * (j : ℝ) ^ 2 +
        (2 * (j : ℝ) + 4) * (2 * (j : ℝ) + 3) *
          ((t : ℝ) ^ 2 / 2 * (2 / (t : ℝ)) ^ 2)) *
            (((2 * j + 2).factorial : ℝ) * (2 / (t : ℝ)) ^ (2 * j + 2)) := by ring
    _ = _ := by rw [ht]; ring

theorem xiGaussianOrientationOrderFactor_monotone : Monotone xiGaussianOrientationOrderFactor := by
  intro j n hjn
  have h : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg j) h 2
  have hp := mul_le_mul
    (show 2 * (j : ℝ) + 4 ≤ 2 * (n : ℝ) + 4 by linarith only [h])
    (show 2 * (j : ℝ) + 3 ≤ 2 * (n : ℝ) + 3 by linarith only [h])
    (show 0 ≤ 2 * (j : ℝ) + 3 by positivity)
    (show 0 ≤ 2 * (n : ℝ) + 4 by positivity)
  unfold xiGaussianOrientationOrderFactor
  nlinarith only [hs, hp]

/-- Every finite order has a coefficient-independent same-time comparison constant. -/
theorem xiGaussianOrientationEnvelope_self_le (n : ℕ) (t : {t : ℝ // 0 < t}) :
    xiGaussianOrientationEnvelope (n + 1) t t ≤
      xiGaussianOrientationOrderFactor n * xiGaussianFourthTraceEnvelope (n + 1) t := by
  unfold xiGaussianOrientationEnvelope xiGaussianFourthTraceEnvelope
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [xiGaussianOrientationMonomialEnvelope_self]
  apply mul_le_mul_of_nonneg_right (xiGaussianOrientationOrderFactor_monotone
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  exact mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (div_nonneg (by positivity) t.property.le) _)

theorem xiGaussianOrientationPhaseBudget_self_le (F : Finset XiZeroCopy) (n : ℕ)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianOrientationPhaseBudget F (n + 1) t t ≤
      (xiGaussianOrientationOrderFactor n * xiResidualOrientationBudget F) *
        xiGaussianFourthTraceEnvelope (n + 1) t := by
  have h := mul_le_mul_of_nonneg_right (xiGaussianOrientationEnvelope_self_le n t)
    (xiResidualOrientationBudget_pos F).le
  simpa only [xiGaussianOrientationPhaseBudget, sub_self, zero_mul, neg_zero,
    Real.exp_zero, one_mul, mul_right_comm] using h

/-- The certified spectral gap makes the complete third-order orientation coefficient
strictly less than three fifths of the exact residual source. -/
theorem xiGaussianThirdOrientation_source_coefficient_lt (F : Finset XiZeroCopy) :
    xiGaussianOrientationOrderFactor 2 * xiResidualOrientationBudget F <
      (3 / 5 : ℝ) * xiCriticalFourthTraceResidual F := by
  have hgap := xiGaussianCertifiedPhaseGap_le_residualPhaseGap F
  rw [xiGaussianCertifiedPhaseGap_eq] at hgap
  have hcoeff : xiGaussianOrientationOrderFactor 2 * 129 <
      (3 / 5 : ℝ) * (128 * xiCriticalResidualPhaseGap F - 129) := by
    unfold xiGaussianOrientationOrderFactor
    nlinarith only [hgap]
  have hfrac : xiGaussianOrientationOrderFactor 2 * 129 /
      (128 * xiCriticalResidualPhaseGap F - 129) < (3 / 5 : ℝ) :=
    (div_lt_iff₀ (xiResidualOrientationDenominator_pos F)).mpr hcoeff
  have h := mul_lt_mul_of_pos_right hfrac (xiCriticalFourthTraceResidual_pos F)
  simpa only [xiResidualOrientationBudget, div_mul_eq_mul_div, mul_div_assoc,
    mul_assoc] using h

/-- A strict saving for the whole third-order phase ceiling at every positive heat time. -/
theorem xiGaussianThirdOrientationPhaseBudget_self_lt (F : Finset XiZeroCopy)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianOrientationPhaseBudget F 3 t t <
      (3 / 5 : ℝ) * xiCriticalFourthTraceResidual F * xiGaussianFourthTraceEnvelope 3 t :=
  (xiGaussianOrientationPhaseBudget_self_le F 2 t).trans_lt
    (mul_lt_mul_of_pos_right (xiGaussianThirdOrientation_source_coefficient_lt F)
      (xiGaussianFourthTraceEnvelope_pos 2 t))

/-- Unlike an untested alternate estimate, this ceiling is strictly smaller than the old
full-source ceiling when compared at the same anchor. -/
theorem xiGaussianThirdOrientationPhaseBudget_self_lt_residual (F : Finset XiZeroCopy)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianOrientationPhaseBudget F 3 t t < xiGaussianResidualPhaseBudget F 3 t t := by
  have h := xiGaussianThirdOrientationPhaseBudget_self_lt F t
  have hcoeff : (3 / 5 : ℝ) < 42 / 41 := by linarith
  have hδ := mul_lt_mul_of_pos_right hcoeff (xiCriticalFourthTraceResidual_pos F)
  have hb := mul_lt_mul_of_pos_right hδ (xiGaussianFourthTraceEnvelope_pos 2 t)
  simpa only [xiGaussianResidualPhaseBudget, sub_self, zero_mul, neg_zero,
    Real.exp_zero, mul_one] using h.trans hb

/-- Complete third-order imaginary energy has the improved source coefficient, uniformly
in all three coefficients and throughout positive heat time. -/
theorem xiGaussianImaginaryChannel_third_le_threeFifths_source
    (F : Finset XiZeroCopy) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range 3, Polynomial.C (a j) * Polynomial.X ^ j) t q) ≤
        ((3 / 5 : ℝ) * xiCriticalFourthTraceResidual F * xiGaussianFourthTraceEnvelope 3 t) *
          (∑ j ∈ Finset.range 3, a j ^ 2) :=
  (xiGaussianImaginaryChannel_le_orientation_budget F 3 a t ⟨t, le_rfl⟩).trans
    (mul_le_mul_of_nonneg_right (xiGaussianThirdOrientationPhaseBudget_self_lt F t).le
      (Finset.sum_nonneg fun j _ => sq_nonneg (a j)))

/-- The independent positive-energy floor combines with the improved complete third-order
phase bound. Every mixed term remains in the literal three-by-three form. -/
theorem exists_xiHeatThirdQuadratic_allTime_threeFifths_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (F : Finset XiZeroCopy) (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        (c₀ * Real.exp (-(L * (t : ℝ))) -
          (3 / 5 : ℝ) * xiCriticalFourthTraceResidual F * xiGaussianFourthTraceEnvelope 3 t) *
            (a ^ 2 + b ^ 2 + c ^ 2) ≤ xiHeatThirdQuadratic a b c t := by
  obtain ⟨c₀, hc₀, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor 3
  refine ⟨c₀, hc₀, L, hL, ?_⟩
  intro F a b c t
  let v : ℕ → ℝ := fun n => if n = 0 then a else if n = 1 then b else c
  have hf := hfloor v t
  have hI := xiGaussianImaginaryChannel_third_le_threeFifths_source F v t
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary
    (∑ j ∈ Finset.range 3, Polynomial.C (v j) * Polynomial.X ^ j) t
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.property] at he
  have hbound :
      (c₀ * Real.exp (-(L * (t : ℝ))) -
        (3 / 5 : ℝ) * xiCriticalFourthTraceResidual F * xiGaussianFourthTraceEnvelope 3 t) *
          (∑ j ∈ Finset.range 3, v j ^ 2) ≤ xiHeatHankelForm 3 v t := by
    nlinarith only [hf, hI, he]
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [v, Finset.sum_range_succ] using hbound

end RHTower
