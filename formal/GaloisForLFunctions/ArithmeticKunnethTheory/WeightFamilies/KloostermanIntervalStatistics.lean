import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanLocalStatistics
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.PrimeResidueMoments
import GaloisForLFunctions.RHTower.Sieve.KloostermanSameModulusIntervalCompletion

/-!
# Interval independence from Kloosterman second moments

Cauchy–Schwarz and the exact second moment bound the complete absolute mass
of the square-root normalized trace by the field size. Chinese remaindering
and periodic completion give the interval independence error `2P/N` without
a pointwise estimate for the trace.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

theorem sum_primeKloostermanTrace_normalized_sq (p : Nat.Primes) :
    (∑ a : ZMod p.val, (primeKloostermanTrace p a / Real.sqrt p.val) ^ 2) =
      (p.val : ℝ) - 1 := by
  simp only [div_pow, Real.sq_sqrt (Nat.cast_nonneg p.val), ← sum_div]
  rw [sum_primeKloostermanTrace_sq]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast p.property.ne_zero)

/-- The complete absolute mass is at most `p`, using only the exact second moment. -/
theorem sum_abs_primeKloostermanTrace_normalized_le (p : Nat.Primes) :
    (∑ a : ZMod p.val, |primeKloostermanTrace p a / Real.sqrt p.val|) ≤ (p.val : ℝ) := by
  have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod p.val))
    (fun _ => (1 : ℝ)) (fun a => |primeKloostermanTrace p a / Real.sqrt p.val|)
  simp only [one_mul, one_pow, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
    mul_one, sq_abs, sum_primeKloostermanTrace_normalized_sq] at h
  apply (sq_le_sq₀ (sum_nonneg fun a _ => abs_nonneg _) hp.le).mp
  exact h.trans (by nlinarith only [hp])

theorem primeResidueMean_normalizedKloosterman (S : Finset Nat.Primes) :
    primeResidueMean S (fun p a => primeKloostermanTrace p a / Real.sqrt p.val) =
      if S = ∅ then 1 else 0 := by
  have hlocal (p : Nat.Primes) :
      (∑ a ∈ range p.val, primeKloostermanTrace p (a : ZMod p.val) / Real.sqrt p.val) = 0 := by
    rw [← RHTower.Sieve.sum_zmod_eq_sum_range_natCast p.val
      (fun a : ZMod p.val => primeKloostermanTrace p a / Real.sqrt p.val), ← sum_div,
      sum_primeKloostermanTrace, zero_div]
  simp only [primeResidueMean, hlocal, zero_div]
  by_cases hS : S = ∅
  · simp [hS]
  · rw [if_neg hS]
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact prod_eq_zero_iff.mpr ⟨p, hp, rfl⟩

/-- Distinct-prime normalized trace products have complete-period absolute mass at most `P`. -/
theorem primeResidueMass_normalizedKloosterman_le (S : Finset Nat.Primes) :
    primeResidueMass S (fun p a => primeKloostermanTrace p a / Real.sqrt p.val) ≤
      (primeSetProduct S : ℝ) := by
  rw [primeResidueMass, primeSetProduct, Nat.cast_prod]
  apply prod_le_prod
  · intro p _
    exact sum_nonneg fun a _ => abs_nonneg _
  · intro p _
    rw [← RHTower.Sieve.sum_zmod_eq_sum_range_natCast p.val
      (fun a : ZMod p.val => |primeKloostermanTrace p a / Real.sqrt p.val|)]
    exact sum_abs_primeKloostermanTrace_normalized_le p

/-- The interval independence error needs no pointwise square-root estimate. -/
theorem abs_sum_Ico_normalizedKloosterman_prod (S : Finset Nat.Primes) (A B : ℕ) :
    |(∑ n ∈ Ico A B, ∏ p ∈ S,
        primeKloostermanTrace p (n : ZMod p.val) / Real.sqrt p.val) -
      ((B - A : ℕ) : ℝ) * (if S = ∅ then 1 else 0)| ≤
        2 * (primeSetProduct S : ℝ) := by
  have h := abs_sum_Ico_primeResidueStatistic_sub_mean S
    (fun p a => primeKloostermanTrace p a / Real.sqrt p.val) A B
  rw [primeResidueMean_normalizedKloosterman] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (primeResidueMass_normalizedKloosterman_le S) (by positivity))

#print axioms sum_abs_primeKloostermanTrace_normalized_le
#print axioms abs_sum_Ico_normalizedKloosterman_prod

/-- Every finite interval average has error at most `2P/N` for normalized traces. -/
theorem abs_average_normalizedKloosterman_prod (S : Finset Nat.Primes) (A N : ℕ) :
    |(∑ n ∈ Ico A (A + (N + 1)), ∏ p ∈ S,
        primeKloostermanTrace p (n : ZMod p.val) / Real.sqrt p.val) / ((N : ℝ) + 1) -
      (if S = ∅ then 1 else 0)| ≤
        2 * (primeSetProduct S : ℝ) / ((N : ℝ) + 1) := by
  have h := abs_sum_Ico_normalizedKloosterman_prod S A (A + (N + 1))
  simp only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_one] at h
  have hN : (0 : ℝ) < N + 1 := by positivity
  have he (x y : ℝ) : x / ((N : ℝ) + 1) - y =
      (x - ((N : ℝ) + 1) * y) / ((N : ℝ) + 1) := by
    rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hN)]
  rw [he, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right h hN.le

#print axioms abs_average_normalizedKloosterman_prod

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
