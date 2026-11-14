import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanMomentHypersurface
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Exact local Kloosterman statistics

The complete prime-field family is centered and has second moment `p(p-1)`.
Deleting the singular parameter changes the mean to `1/(p-1)` and the
normalized variance to `1 - 1/(p-1)^2`. These exact identities isolate the
local centering correction in Kloosterman fluctuation statistics.
-/

open Finset AddChar

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

open SignedSuccessorArithmetic

noncomputable section

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The real Kloosterman trace with fixed second frequency one. -/
def primeKloostermanTrace (p : Nat.Primes) (a : ZMod p.val) : ℝ :=
  (kloosterman ZMod.stdAddChar a 1).re

theorem card_primeKloostermanParameters (p : Nat.Primes) :
    ((univ : Finset (ZMod p.val)).erase 0).card = p.val - 1 := by
  rw [card_erase_of_mem (mem_univ (0 : ZMod p.val)), card_univ, ZMod.card]

theorem primeKloostermanTrace_im (p : Nat.Primes) (a : ZMod p.val) :
    (kloosterman ZMod.stdAddChar a 1).im = 0 := by
  have h := congrArg Complex.im (kloosterman_conj ZMod.stdAddChar a 1)
  rw [Complex.conj_im] at h
  linarith only [h]

theorem normSq_primeKloostermanTrace (p : Nat.Primes) (a : ZMod p.val) :
    Complex.normSq (kloosterman ZMod.stdAddChar a 1) = primeKloostermanTrace p a ^ 2 := by
  rw [Complex.normSq_apply, primeKloostermanTrace_im]
  simp only [primeKloostermanTrace, mul_zero, add_zero, sq]

/-- Complete parameter averaging kills every nonzero additive frequency. -/
theorem sum_primeKloostermanTrace (p : Nat.Primes) :
    ∑ a : ZMod p.val, primeKloostermanTrace p a = 0 := by
  have h : ∑ a : ZMod p.val, kloosterman ZMod.stdAddChar a 1 = 0 := by
    unfold kloosterman
    rw [sum_comm]
    apply sum_eq_zero
    intro x hx
    have hx0 : x ≠ 0 := (mem_filter.mp hx).2
    simp_rw [map_add_eq_mul]
    rw [← sum_mul, sum_mulShift x (ZMod.isPrimitive_stdAddChar p.val), if_neg hx0]
    simp only [Nat.cast_zero, zero_mul]
  simpa only [Complex.re_sum, Complex.zero_re, primeKloostermanTrace] using
    congrArg Complex.re h

theorem primeKloostermanTrace_zero (p : Nat.Primes) :
    primeKloostermanTrace p 0 = -1 := by
  unfold primeKloostermanTrace
  rw [kloosterman_zero_left (ZMod.isPrimitive_stdAddChar p.val) one_ne_zero]
  simp

/-- The punctured family has total trace one. -/
theorem sum_primeKloostermanTrace_ne_zero (p : Nat.Primes) :
    ∑ a ∈ (univ : Finset (ZMod p.val)).erase 0, primeKloostermanTrace p a = 1 := by
  rw [sum_erase_eq_sub (mem_univ 0), sum_primeKloostermanTrace,
    primeKloostermanTrace_zero]
  ring

/-- Exact raw second moment of the real complete family. -/
theorem sum_primeKloostermanTrace_sq (p : Nat.Primes) :
    ∑ a : ZMod p.val, primeKloostermanTrace p a ^ 2 =
      (p.val : ℝ) * (p.val - 1) := by
  simp_rw [← normSq_primeKloostermanTrace]
  simpa only [ZMod.card] using
    sum_normSq_kloosterman (ZMod.isPrimitive_stdAddChar p.val) (1 : ZMod p.val)

/-- Removing the zero parameter removes exactly one unit of second moment. -/
theorem sum_primeKloostermanTrace_sq_ne_zero (p : Nat.Primes) :
    ∑ a ∈ (univ : Finset (ZMod p.val)).erase 0, primeKloostermanTrace p a ^ 2 =
      (p.val : ℝ) ^ 2 - p.val - 1 := by
  rw [sum_erase_eq_sub (mem_univ 0), sum_primeKloostermanTrace_sq,
    primeKloostermanTrace_zero]
  ring

/-- The second symmetric-power statistic has an exact negative local bias. -/
theorem mean_primeKloostermanTrace_second_character (p : Nat.Primes) :
    (∑ a ∈ (univ : Finset (ZMod p.val)).erase 0,
      (primeKloostermanTrace p a ^ 2 / (p.val : ℝ) - 1)) / ((p.val : ℝ) - 1) =
        -1 / ((p.val : ℝ) * (p.val - 1)) := by
  have hp : 1 ≤ p.val := p.property.one_lt.le
  have hpR : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hp0 : (p.val : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hpR)
  have hp1 : (p.val : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpR)
  rw [sum_sub_distrib, ← sum_div, sum_primeKloostermanTrace_sq_ne_zero]
  simp only [sum_const, nsmul_eq_mul, mul_one, card_primeKloostermanParameters,
    Nat.cast_sub hp, Nat.cast_one]
  field_simp [hp0, hp1]
  ring

/-- The second cosine statistic differs from its Sato–Tate limit by an exact rational term. -/
theorem mean_primeKloostermanTrace_second_cosine (p : Nat.Primes) :
    (∑ a ∈ (univ : Finset (ZMod p.val)).erase 0,
      (primeKloostermanTrace p a ^ 2 / (2 * (p.val : ℝ)) - 1)) /
        ((p.val : ℝ) - 1) = -(1 / 2 : ℝ) - 1 / (2 * (p.val : ℝ) * (p.val - 1)) := by
  have hp : 1 ≤ p.val := p.property.one_lt.le
  have hpR : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hp0 : (p.val : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hpR)
  have hp1 : (p.val : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpR)
  rw [sum_sub_distrib, ← sum_div, sum_primeKloostermanTrace_sq_ne_zero]
  simp only [sum_const, nsmul_eq_mul, mul_one, card_primeKloostermanParameters,
    Nat.cast_sub hp, Nat.cast_one]
  field_simp [hp0, hp1]
  ring

/-- Centering the punctured family retains its exact finite-prime correction. -/
theorem sum_primeKloostermanTrace_centered_sq (p : Nat.Primes) :
    ∑ a ∈ (univ : Finset (ZMod p.val)).erase 0,
      (primeKloostermanTrace p a - 1 / ((p.val : ℝ) - 1)) ^ 2 =
        (p.val : ℝ) ^ 2 - p.val - 1 - 1 / ((p.val : ℝ) - 1) := by
  have hp : 1 ≤ p.val := p.property.one_lt.le
  have hpR : (p.val : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
    linarith
  have he (x : ℝ) : (x - 1 / ((p.val : ℝ) - 1)) ^ 2 =
      x ^ 2 - (2 / ((p.val : ℝ) - 1)) * x + 1 / ((p.val : ℝ) - 1) ^ 2 := by
    field_simp [hpR]
    ring
  simp_rw [he]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_primeKloostermanTrace_sq_ne_zero, sum_primeKloostermanTrace_ne_zero]
  simp only [sum_const, nsmul_eq_mul, card_primeKloostermanParameters,
    Nat.cast_sub hp, Nat.cast_one]
  field_simp [hpR]
  ring

/-- The variance of `K/√p` over nonzero parameters is `1 - 1/(p-1)^2`. -/
theorem primeKloostermanTrace_normalized_variance (p : Nat.Primes) :
    (∑ a ∈ (univ : Finset (ZMod p.val)).erase 0,
      (primeKloostermanTrace p a - 1 / ((p.val : ℝ) - 1)) ^ 2) /
        ((p.val : ℝ) * (p.val - 1)) = 1 - 1 / ((p.val : ℝ) - 1) ^ 2 := by
  rw [sum_primeKloostermanTrace_centered_sq]
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hp0 : (p.val : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hp1 : (p.val : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  field_simp [hp0, hp1]
  ring

#print axioms sum_primeKloostermanTrace
#print axioms sum_primeKloostermanTrace_sq
#print axioms mean_primeKloostermanTrace_second_character
#print axioms mean_primeKloostermanTrace_second_cosine
#print axioms primeKloostermanTrace_normalized_variance

end

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
