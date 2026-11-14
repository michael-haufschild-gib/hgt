import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanFourthMoment
import Mathlib.Probability.CentralLimitTheorem

/-!
# Standardized empirical Kloosterman laws

Uniform sampling of the complete prime-field family, divided by `√(p-1)`,
has mean zero and variance one. The exact fourth moment bounds its kurtosis
by three, uniformly in the prime, and its third absolute moment by two.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- Variance-one normalization of the complete Kloosterman family. -/
def standardizedKloostermanTrace (p : Nat.Primes) (a : ZMod p.val) : ℝ :=
  primeKloostermanTrace p a / Real.sqrt ((p.val : ℝ) - 1)

/-- The empirical distribution with one atom for every prime-field parameter. -/
def primeKloostermanLaw (p : Nat.Primes) : Measure ℝ :=
  (p.val : ℝ≥0∞)⁻¹ • ∑ a : ZMod p.val, Measure.dirac (standardizedKloostermanTrace p a)

instance (p : Nat.Primes) : IsProbabilityMeasure (primeKloostermanLaw p) := by
  constructor
  have hp : (p.val : ℝ≥0∞) ≠ 0 := by exact_mod_cast p.property.ne_zero
  simp [primeKloostermanLaw, Measure.coe_finsetSum, ZMod.card, hp]

/-- Finite support makes every real or complex test function integrable. -/
theorem integrable_primeKloostermanLaw (p : Nat.Primes)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable f (primeKloostermanLaw p) := by
  have hp : (p.val : ℝ≥0∞) ≠ 0 := by exact_mod_cast p.property.ne_zero
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr hp)
  exact integrable_finsetSum_measure.mpr fun _ _ => integrable_dirac (by simp)

/-- Integration is the finite parameter average, with multiplicities retained. -/
theorem integral_primeKloostermanLaw (p : Nat.Primes)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) :
    ∫ x, f x ∂primeKloostermanLaw p =
      (p.val : ℝ)⁻¹ • ∑ a : ZMod p.val, f (standardizedKloostermanTrace p a) := by
  rw [primeKloostermanLaw, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]

theorem integral_primeKloostermanLaw_id (p : Nat.Primes) :
    ∫ x, x ∂primeKloostermanLaw p = 0 := by
  rw [integral_primeKloostermanLaw]
  simp only [standardizedKloostermanTrace, ← sum_div, sum_primeKloostermanTrace,
    zero_div, smul_zero]

theorem integral_primeKloostermanLaw_sq (p : Nat.Primes) :
    ∫ x, x ^ 2 ∂primeKloostermanLaw p = 1 := by
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  rw [integral_primeKloostermanLaw]
  simp only [standardizedKloostermanTrace, div_pow, Real.sq_sqrt (by linarith :
    0 ≤ (p.val : ℝ) - 1), ← sum_div, sum_primeKloostermanTrace_sq, smul_eq_mul]
  field_simp

/-- The standardized fourth moment is bounded uniformly, including characteristic two. -/
theorem integral_primeKloostermanLaw_four_le (p : Nat.Primes) :
    ∫ x, x ^ 4 ∂primeKloostermanLaw p ≤ 3 := by
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hsq : Real.sqrt ((p.val : ℝ) - 1) ^ 4 = ((p.val : ℝ) - 1) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by linarith)]
  rw [integral_primeKloostermanLaw]
  simp only [standardizedKloostermanTrace, div_pow, hsq, ← sum_div, smul_eq_mul]
  rw [inv_mul_eq_div, div_div, div_le_iff₀ (by positivity :
    0 < ((p.val : ℝ) - 1) ^ 2 * p.val), sum_primeKloostermanTrace_four]
  have h := mul_nonneg (by linarith : (0 : ℝ) ≤ p.val)
    (sq_nonneg ((p.val : ℝ) - 2))
  split_ifs <;> nlinarith only [h, hp]

/-- The third absolute moment needed for characteristic-function replacement is uniform. -/
theorem integral_primeKloostermanLaw_abs_cube_le (p : Nat.Primes) :
    ∫ x, |x| ^ 3 ∂primeKloostermanLaw p ≤ 2 := by
  have hpoint (x : ℝ) : |x| ^ 3 ≤ (x ^ 2 + x ^ 4) / 2 := by
    have h := mul_nonneg (sq_nonneg x) (sq_nonneg (|x| - 1))
    nlinarith only [h, sq_abs x]
  have h := integral_mono (integrable_primeKloostermanLaw p _)
    (integrable_primeKloostermanLaw p _) hpoint
  rw [integral_div, integral_add (integrable_primeKloostermanLaw p _)
    (integrable_primeKloostermanLaw p _), integral_primeKloostermanLaw_sq] at h
  linarith only [h, integral_primeKloostermanLaw_four_le p]

#print axioms integral_primeKloostermanLaw_id
#print axioms integral_primeKloostermanLaw_sq
#print axioms integral_primeKloostermanLaw_four_le
#print axioms integral_primeKloostermanLaw_abs_cube_le

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
