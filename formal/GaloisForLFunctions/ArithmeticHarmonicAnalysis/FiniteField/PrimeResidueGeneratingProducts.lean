import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.PrimeResidueDistribution
import Mathlib.Tactic.Ring

/-!
# Exact generating-product moments on prime residue coordinates

Centering the indicator of any forbidden residue set gives a local factor of mean one.
Chinese remaindering makes the full product have mean one and factors its second moment
exactly. All residue sets are allowed, including empty and full sets; no independence premise
is required. These are the finite-period moment identities behind generating-polynomial sieves.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

noncomputable section

/-- The centered local generating factor, with its denominator cleared. -/
def centeredResidueFactor {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (t : ℝ) (a : α) : ℝ :=
  if a ∈ A then 1 - t * (Fintype.card α - (A.card : ℝ)) else 1 + t * A.card

private theorem sum_two_values {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (x y : ℝ) :
    (∑ a : α, if a ∈ A then x else y) =
      A.card * x + (Fintype.card α - (A.card : ℝ)) * y := by
  rw [sum_ite]
  simp only [filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
  have heq : univ.filter (fun a => a ∉ A) = univ \ A := by ext a; simp
  rw [heq, card_sdiff (subset_univ _), card_univ, Nat.cast_sub (card_le_univ A)]

/-- The local factor has mean one under the uniform law on residues. -/
theorem sum_centeredResidueFactor {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (t : ℝ) :
    ∑ a : α, centeredResidueFactor A t a = Fintype.card α := by
  simp only [centeredResidueFactor]
  rw [sum_two_values]
  ring

/-- The local second moment is exactly one plus the Bernoulli variance term. -/
theorem sum_centeredResidueFactor_sq {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (t : ℝ) :
    ∑ a : α, (centeredResidueFactor A t a) ^ 2 =
      Fintype.card α * (1 + t ^ 2 * A.card * (Fintype.card α - (A.card : ℝ))) := by
  simp only [centeredResidueFactor, ite_pow]
  rw [sum_two_values]
  ring

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- Chinese remaindering evaluates the generating product's complete-period first moment. -/
theorem sum_prime_centered_product (S : Finset Nat.Primes)
    (A : (p : Nat.Primes) → Finset (ZMod p.val)) (t : Nat.Primes → ℝ) :
    ∑ n ∈ range (primeSetProduct S), ∏ p ∈ S, centeredResidueFactor (A p) (t p) (n : ZMod p.val) =
      primeSetProduct S := by
  rw [sum_primeResidue_product]
  simp only [sum_centeredResidueFactor, ZMod.card, primeSetProduct, Nat.cast_prod]

/-- The exact second moment multiplies the local variances, even when forbidden sets vary by prime. -/
theorem sum_prime_centered_product_sq (S : Finset Nat.Primes)
    (A : (p : Nat.Primes) → Finset (ZMod p.val)) (t : Nat.Primes → ℝ) :
    ∑ n ∈ range (primeSetProduct S),
      (∏ p ∈ S, centeredResidueFactor (A p) (t p) (n : ZMod p.val)) ^ 2 =
      (primeSetProduct S : ℝ) *
        ∏ p ∈ S, (1 + t p ^ 2 * (A p).card * (p.val - ((A p).card : ℝ))) := by
  simp_rw [prod_pow]
  rw [sum_primeResidue_product]
  simp only [sum_centeredResidueFactor_sq, ZMod.card, prod_mul_distrib,
    primeSetProduct, Nat.cast_prod]

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
