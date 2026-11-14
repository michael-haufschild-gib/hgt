import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanProbabilityLaw
import GaloisForLFunctions.RHTower.WeilKloostermanBound

/-!
# Uniform support of standardized Kloosterman laws

Inversion identifies the two-frequency trace with the normalization used in
Weil's bound. The singular parameter and characteristic two satisfy the same
bound directly. Division by the exact standard deviation gives support in
the fixed interval `[-3,3]` for every prime.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

private theorem kloosterman_one_eq_weil (p : Nat.Primes) (a : ZMod p.val) :
    SignedSuccessorArithmetic.kloosterman ZMod.stdAddChar a 1 =
      RHTower.WeilKloosterman.kloosterman ZMod.stdAddChar a := by
  have hr : RHTower.WeilKloosterman.kloosterman ZMod.stdAddChar a =
      ∑ x ∈ (univ : Finset (ZMod p.val)).filter (· ≠ 0),
        ZMod.stdAddChar (x + a * x⁻¹) := by
    simp only [RHTower.WeilKloosterman.kloosterman, sum_filter, ne_eq, ite_not, div_eq_mul_inv]
  rw [SignedSuccessorArithmetic.kloosterman, hr]
  refine sum_nbij' (fun x : ZMod p.val => x⁻¹) (fun x => x⁻¹)
    (by simp) (by simp) (by simp) (by simp) ?_
  intro x _
  congr 1
  simp only [one_mul, inv_inv]
  ring

/-- The elementary bound handles small fields without an exceptional hypothesis. -/
theorem abs_primeKloostermanTrace_le_card (p : Nat.Primes) (a : ZMod p.val) :
    |primeKloostermanTrace p a| ≤ (p.val : ℝ) - 1 := by
  unfold primeKloostermanTrace
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [SignedSuccessorArithmetic.kloosterman]
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe, sum_const, nsmul_eq_mul, mul_one,
    SignedSuccessorArithmetic.card_units_filter, ZMod.card,
    Nat.cast_sub p.property.one_le, Nat.cast_one]

/-- Weil's bound holds for every complete prime-field parameter, including zero and characteristic two. -/
theorem abs_primeKloostermanTrace_le_two_sqrt (p : Nat.Primes) (a : ZMod p.val) :
    |primeKloostermanTrace p a| ≤ 2 * Real.sqrt (p.val : ℝ) := by
  have hs : (1 : ℝ) ≤ Real.sqrt (p.val : ℝ) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ p.val by exact_mod_cast p.property.one_le)
  by_cases hp2 : p.val = 2
  · have h := abs_primeKloostermanTrace_le_card p a
    norm_num only [hp2, Nat.cast_ofNat] at h
    linarith only [h, hs]
  by_cases ha : a = 0
  · subst a
    rw [primeKloostermanTrace_zero, abs_neg, abs_one]
    linarith only [hs]
  unfold primeKloostermanTrace
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [kloosterman_one_eq_weil]
  exact RHTower.WeilKloosterman.kloosterman_weil_bound hp2 ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar p.val) ha

/-- Exact variance normalization leaves all local distributions in one fixed compact interval. -/
theorem abs_standardizedKloostermanTrace_le_three (p : Nat.Primes) (a : ZMod p.val) :
    |standardizedKloostermanTrace p a| ≤ 3 := by
  have hp : (2 : ℝ) ≤ p.val := by exact_mod_cast p.property.two_le
  have hs : 0 < Real.sqrt ((p.val : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  rw [standardizedKloostermanTrace, abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  refine (abs_primeKloostermanTrace_le_two_sqrt p a).trans ?_
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ p.val),
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ p.val - 1)]
  nlinarith only [hp]

#print axioms abs_primeKloostermanTrace_le_two_sqrt
#print axioms abs_standardizedKloostermanTrace_le_three

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
