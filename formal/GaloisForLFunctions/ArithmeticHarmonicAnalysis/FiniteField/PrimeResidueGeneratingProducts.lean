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
  rw [heq, card_sdiff, inter_univ, card_univ, Nat.cast_sub (card_le_univ A)]

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

/-- The centered generating product across the chosen prime coordinates. -/
def centeredPrimeResidueProduct (S : Finset Nat.Primes)
    (A : (p : Nat.Primes) → Finset (ZMod p.val)) (t : Nat.Primes → ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ S, centeredResidueFactor (A p) (t p) (n : ZMod p.val)

/-- Chinese remaindering evaluates the generating product's complete-period first moment. -/
theorem sum_prime_centered_product (S : Finset Nat.Primes)
    (A : (p : Nat.Primes) → Finset (ZMod p.val)) (t : Nat.Primes → ℝ) :
    ∑ n ∈ range (primeSetProduct S), centeredPrimeResidueProduct S A t n =
      primeSetProduct S := by
  unfold centeredPrimeResidueProduct
  rw [sum_primeResidue_product]
  simp only [sum_centeredResidueFactor, ZMod.card, primeSetProduct, Nat.cast_prod]

/-- The exact second moment multiplies the local variances, even when forbidden sets vary by prime. -/
theorem sum_prime_centered_product_sq (S : Finset Nat.Primes)
    (A : (p : Nat.Primes) → Finset (ZMod p.val)) (t : Nat.Primes → ℝ) :
    ∑ n ∈ range (primeSetProduct S),
      (centeredPrimeResidueProduct S A t n) ^ 2 =
      (primeSetProduct S : ℝ) *
        ∏ p ∈ S, (1 + t p ^ 2 * (A p).card * (p.val - ((A p).card : ℝ))) := by
  calc
    _ = ∑ n ∈ range (primeSetProduct S),
        ∏ p ∈ S, (centeredResidueFactor (A p) (t p) (n : ZMod p.val)) ^ 2 := by
      apply sum_congr rfl
      intro n _
      exact (prod_pow S 2 (fun p : Nat.Primes =>
        centeredResidueFactor (A p) (t p) (n : ZMod p.val))).symm
    _ = ∏ p ∈ S, ∑ a : ZMod p.val, (centeredResidueFactor (A p) (t p) a) ^ 2 :=
      sum_primeResidue_product S (fun p a => (centeredResidueFactor (A p) (t p) a) ^ 2)
    _ = _ := by
      simp only [sum_centeredResidueFactor_sq, ZMod.card, prod_mul_distrib,
        primeSetProduct, Nat.cast_prod]

/-- Subtracting the exact mean leaves the product variance minus one, without absolute-value loss. -/
theorem sum_prime_centered_product_variance (S : Finset Nat.Primes)
    (A : (p : Nat.Primes) → Finset (ZMod p.val)) (t : Nat.Primes → ℝ) :
    ∑ n ∈ range (primeSetProduct S),
      ((centeredPrimeResidueProduct S A t n) - 1) ^ 2 =
      (primeSetProduct S : ℝ) *
        ((∏ p ∈ S, (1 + t p ^ 2 * (A p).card * (p.val - ((A p).card : ℝ)))) - 1) := by
  simp_rw [sub_sq, mul_one, one_pow]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_prime_centered_product_sq, sum_prime_centered_product]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  ring

/-- A complete-period deviation bound for arbitrary forbidden residue sets and local parameters. -/
theorem prime_centered_product_deviation (S : Finset Nat.Primes)
    (A : (p : Nat.Primes) → Finset (ZMod p.val)) (t : Nat.Primes → ℝ) (L : NNReal) :
    (L : ℝ) ^ 2 * (((range (primeSetProduct S)).filter fun n =>
      (L : ℝ) ≤ |(centeredPrimeResidueProduct S A t n) - 1|).card : ℝ) ≤
      (primeSetProduct S : ℝ) *
        ((∏ p ∈ S, (1 + t p ^ 2 * (A p).card * (p.val - ((A p).card : ℝ)))) - 1) := by
  rw [← sum_prime_centered_product_variance]
  calc
    _ = ∑ _n ∈ (range (primeSetProduct S)).filter (fun n =>
        (L : ℝ) ≤ |(centeredPrimeResidueProduct S A t n) - 1|),
          (L : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ n ∈ (range (primeSetProduct S)).filter (fun n =>
        (L : ℝ) ≤ |(centeredPrimeResidueProduct S A t n) - 1|),
          ((centeredPrimeResidueProduct S A t n) - 1) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hbound : (L : ℝ) ≤ |centeredPrimeResidueProduct S A t n - 1| :=
        (mem_filter.mp hn).2
      calc
        _ ≤ |centeredPrimeResidueProduct S A t n - 1| ^ 2 :=
          pow_le_pow_left₀ L.property hbound 2
        _ = _ := sq_abs _
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun n _ _ => sq_nonneg _)

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.sum_prime_centered_product
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.sum_prime_centered_product_sq
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.sum_prime_centered_product_variance
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.prime_centered_product_deviation
