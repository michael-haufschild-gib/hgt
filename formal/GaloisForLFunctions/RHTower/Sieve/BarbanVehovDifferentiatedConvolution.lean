import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorFullLongMomentExpansion

/-!
# The differentiated Barban--Vehov coefficient as a von-Mangoldt convolution

Logarithmic differentiation of the complementary divisor turns the base Barban--Vehov coefficient
into its Dirichlet convolution with `Λ`, with a minus sign. This gives the cross and derivative
long moments their canonical convolutional normal form.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Barban--Vehov truncation weight as a real arithmetic function. -/
def barbanVehovWeightArithmetic (M : ℕ) : ArithmeticFunction ℝ :=
  { toFun := barbanVehovWeight M
    map_zero' := by simp [barbanVehovWeight] }

@[simp] theorem barbanVehovWeightArithmetic_apply (M n : ℕ) :
    barbanVehovWeightArithmetic M n = barbanVehovWeight M n := rfl

theorem barbanVehovCoeff_eq_weightArithmetic_mul_zeta (M k : ℕ) :
    barbanVehovCoeff M k =
      (barbanVehovWeightArithmetic M * (ζ : ArithmeticFunction ℝ)) k := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rfl

theorem barbanVehovDifferentiatedCoeff_eq_neg_weightArithmetic_mul_log
    {M k : ℕ} (hk : 0 < k) :
    barbanVehovDifferentiatedCoeff M k =
      -((barbanVehovWeightArithmetic M * ArithmeticFunction.log) k) := by
  rw [barbanVehovDifferentiatedCoeff, barbanVehovLogMomentCoeff, barbanVehovCoeff]
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal
    (fun q r => barbanVehovWeightArithmetic M q * ArithmeticFunction.log r)]
  simp only [barbanVehovWeightArithmetic_apply, ArithmeticFunction.log_apply]
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [log_natDiv_eq_sub_log_of_dvd hk (Nat.dvd_of_mem_divisors hq)]
  ring

theorem barbanVehovDifferentiatedCoeff_eq_neg_sum_weight_logNatDiv
    {M k : ℕ} (hk : 0 < k) :
    barbanVehovDifferentiatedCoeff M k =
      -∑ q ∈ k.divisors,
        barbanVehovWeight M q * Real.log (((k / q : ℕ) : ℝ)) := by
  rw [barbanVehovDifferentiatedCoeff_eq_neg_weightArithmetic_mul_log hk,
    ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal
    (fun q r => barbanVehovWeightArithmetic M q * ArithmeticFunction.log r)]
  simp only [barbanVehovWeightArithmetic_apply, ArithmeticFunction.log_apply]

/-- The differentiated coefficient is minus the von-Mangoldt convolution of the base coefficient. -/
theorem barbanVehovDifferentiatedCoeff_eq_neg_coeff_mul_vonMangoldt
    {M k : ℕ} (hk : 0 < k) :
    barbanVehovDifferentiatedCoeff M k =
      -(((barbanVehovWeightArithmetic M * (ζ : ArithmeticFunction ℝ)) * Λ) k) := by
  rw [mul_assoc, ArithmeticFunction.zeta_mul_vonMangoldt]
  exact barbanVehovDifferentiatedCoeff_eq_neg_weightArithmetic_mul_log hk

/-- Divisor-sum form of the differentiated convolution identity. -/
theorem barbanVehovDifferentiatedCoeff_eq_neg_sum_vonMangoldt
    {M k : ℕ} (hk : 0 < k) :
    barbanVehovDifferentiatedCoeff M k =
      -∑ d ∈ k.divisors, barbanVehovCoeff M d * Λ (k / d) := by
  rw [barbanVehovDifferentiatedCoeff_eq_neg_coeff_mul_vonMangoldt hk,
    ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal
    (fun d q => (barbanVehovWeightArithmetic M * (ζ : ArithmeticFunction ℝ)) d * Λ q)]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro d hd
  rw [← barbanVehovCoeff_eq_weightArithmetic_mul_zeta]

/-- Literal von-Mangoldt convolution of the Barban--Vehov coefficient. -/
def barbanVehovVonMangoldtConvolution (M k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors, barbanVehovCoeff M d * Λ (k / d)

theorem barbanVehovDifferentiatedCoeff_eq_neg_vonMangoldtConvolution
    {M k : ℕ} (hk : 0 < k) :
    barbanVehovDifferentiatedCoeff M k = -barbanVehovVonMangoldtConvolution M k := by
  exact barbanVehovDifferentiatedCoeff_eq_neg_sum_vonMangoldt hk

end

end RHTower.Sieve

namespace RHTower

noncomputable section

theorem levinsonCriticalDetectorFullLongCrossMoment_eq_neg_vonMangoldtConvolution
    (L M : ℕ) :
    levinsonCriticalDetectorFullLongCrossMoment L M =
      -∑ k ∈ Finset.Ioc L (L * M),
        Sieve.barbanVehovCoeff M k * Sieve.barbanVehovVonMangoldtConvolution M k / (k : ℝ) := by
  rw [levinsonCriticalDetectorFullLongCrossMoment, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Sieve.barbanVehovDifferentiatedCoeff_eq_neg_vonMangoldtConvolution
    (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hk).1)]
  ring

theorem levinsonCriticalDetectorFullLongDerivativeMoment_eq_vonMangoldtConvolution
    (L M : ℕ) :
    levinsonCriticalDetectorFullLongDerivativeMoment L M =
      ∑ k ∈ Finset.Ioc L (L * M),
        Sieve.barbanVehovVonMangoldtConvolution M k ^ 2 / (k : ℝ) := by
  rw [levinsonCriticalDetectorFullLongDerivativeMoment]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Sieve.barbanVehovDifferentiatedCoeff_eq_neg_vonMangoldtConvolution
    (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hk).1)]
  ring

end


end RHTower
