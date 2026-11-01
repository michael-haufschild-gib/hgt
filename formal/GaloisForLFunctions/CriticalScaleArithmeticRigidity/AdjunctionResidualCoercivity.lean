import GaloisForLFunctions.CriticalScaleArithmeticRigidity.RelativePrimeResidual
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheConductorTwoIsTheFirstExcitation

/-!
# The prime residual is small relative to adjunction energy

Removing the constant conductor leaves the exact arithmetic excitation
gap `2 log 2`. The source-relative residual estimate then has a quadratic
logarithmic conductor cost, with no coefficient-mass term remaining.
The coefficient projection here is distinct from the finite-horizon
orthogonal projection against the Weil pole.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticIntersectionTheory RenormalizedArithmeticPotentialTheory
  SignedArithmeticHodgeTheory

/-- Remove the constant conductor in the arithmetic coefficient space. -/
def removeConstantConductor (a : ℕ → ℝ) (m : ℕ) : ℝ := if m = 1 then 0 else a m

/-- The constant conductor carries no adjunction energy. -/
theorem primeAdjunctionMass_removeConstantConductor (Q : ℕ) (a : ℕ → ℝ) :
    primeAdjunctionMass Q (removeConstantConductor a) = primeAdjunctionMass Q a := by
  apply sum_congr rfl
  intro m _
  by_cases hm : m = 1
  · subst m
    simp only [removeConstantConductor, Nat.cast_one, Real.log_one,
      SelectiveMultiscaleArithmeticPositivity.tameDifferent_one, zero_add, zero_mul]
  · simp only [removeConstantConductor, if_neg hm]

/-- The exact first arithmetic excitation controls every nonconstant coefficient. -/
theorem coefficient_mass_le_adjunction_gap (Q : ℕ) (a : ℕ → ℝ) :
    (2 * Real.log 2) * (∑ m ∈ Icc 1 Q, removeConstantConductor a m ^ 2) ≤
      primeAdjunctionMass Q a := by
  rw [mul_sum, primeAdjunctionMass]
  apply sum_le_sum
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    simp only [removeConstantConductor, if_true, zero_pow two_ne_zero,
      mul_zero, Nat.cast_one, Real.log_one,
      SelectiveMultiscaleArithmeticPositivity.tameDifferent_one, zero_add, zero_mul, le_refl]
  · rw [removeConstantConductor, if_neg hm1]
    have hgap := (SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_sub_one_ge
      (show 2 ≤ m by have := (mem_Icc.mp hm).1; omega)).1
    rw [SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_one,
      ramanujanAdjunctionEnergy] at hgap
    have hweight : 2 * Real.log 2 ≤ Real.log m + tameDifferent m := by linarith only [hgap]
    exact mul_le_mul_of_nonneg_right hweight (sq_nonneg _)

/-- The literal prime residual costs only two conductor logarithms relative to exact
adjunction energy after the constant coefficient is removed. -/
theorem exists_primeResidual_removeConstant_relative_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q N : ℕ, 2 ≤ Q → 2 ≤ N → ∀ a : ℕ → ℝ,
      (∑ n ∈ Icc 1 N,
        (∑ m ∈ Icc 1 Q, removeConstantConductor a m * ramanujanPrimeResidual m N n) ^ 2) /
          Real.log N ≤
        C * (1 + Real.log Q) ^ 2 / Real.log N * primeAdjunctionMass Q a := by
  obtain ⟨C, hC, hres⟩ := exists_primeResidual_packet_relative_log_sq_le
  have hgap : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨C / (2 * Real.log 2) + 532, by positivity, ?_⟩
  intro Q N hQ hN a
  have h := hres Q N hQ hN (removeConstantConductor a)
  rw [primeAdjunctionMass_removeConstantConductor] at h
  have hM := coefficient_mass_le_adjunction_gap Q a
  have hL := primeAdjunctionMass_nonneg Q a
  have hH : 0 ≤ 1 + Real.log (Q : ℝ) := by positivity
  have hH2 : 1 + Real.log (Q : ℝ) ≤ (1 + Real.log (Q : ℝ)) ^ 2 := by
    nlinarith only [Real.log_natCast_nonneg Q, sq_nonneg (Real.log (Q : ℝ))]
  have hCM : C * (∑ m ∈ Icc 1 Q, removeConstantConductor a m ^ 2) ≤
      (C / (2 * Real.log 2)) * primeAdjunctionMass Q a := by
    calc
      _ = (C / (2 * Real.log 2)) *
          ((2 * Real.log 2) * ∑ m ∈ Icc 1 Q, removeConstantConductor a m ^ 2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hgap.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (div_nonneg hC.le hgap.le)
  have hlinear := mul_le_mul_of_nonneg_left hCM hH
  have hquadratic := mul_le_mul_of_nonneg_right hH2
    (mul_nonneg (div_nonneg hC.le hgap.le) hL)
  have hnum :
      C * (1 + Real.log Q) * (∑ m ∈ Icc 1 Q, removeConstantConductor a m ^ 2) +
          532 * (1 + Real.log Q) ^ 2 * primeAdjunctionMass Q a ≤
        (C / (2 * Real.log 2) + 532) * (1 + Real.log Q) ^ 2 * primeAdjunctionMass Q a := by
    nlinarith only [hlinear, hquadratic]
  exact (h.trans (div_le_div_of_nonneg_right hnum (Real.log_natCast_nonneg N))).trans_eq (by ring)

#print axioms coefficient_mass_le_adjunction_gap
#print axioms exists_primeResidual_removeConstant_relative_sq_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
