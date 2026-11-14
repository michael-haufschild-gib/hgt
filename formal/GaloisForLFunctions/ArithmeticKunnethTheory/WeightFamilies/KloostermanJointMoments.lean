import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanLocalStatistics
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.PrimeResidueMoments
import GaloisForLFunctions.RHTower.Sieve.KloostermanSameModulusIntervalCompletion

/-!
# Joint Kloosterman moments across distinct primes

The Chinese remainder theorem gives exact independence over a squarefree
period, for arbitrary powers of the real prime-field Kloosterman trace.
The first two local moments therefore give exact joint centering and energy,
with the finite-prime corrections retained.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

noncomputable section

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- Every joint moment factors into its complete local moments. -/
theorem sum_primeKloostermanTrace_joint_moment (S : Finset Nat.Primes)
    (r : Nat.Primes → ℕ) :
    (∑ n ∈ range (primeSetProduct S),
      ∏ p ∈ S, primeKloostermanTrace p (n : ZMod p.val) ^ r p) =
      ∏ p ∈ S, ∑ a : ZMod p.val, primeKloostermanTrace p a ^ r p := by
  rw [sum_range_primeSetProduct_prod S _
    (fun p => primeResidue_local_periodic p (fun a => primeKloostermanTrace p a ^ r p))]
  apply prod_congr rfl
  intro p _
  exact (RHTower.Sieve.sum_zmod_eq_sum_range_natCast p.val
    (fun a : ZMod p.val => primeKloostermanTrace p a ^ r p)).symm

/-- Every nonempty product of distinct-prime traces is exactly centered. -/
theorem sum_primeKloostermanTrace_prod (S : Finset Nat.Primes) :
    (∑ n ∈ range (primeSetProduct S),
      ∏ p ∈ S, primeKloostermanTrace p (n : ZMod p.val)) =
      if S = ∅ then 1 else 0 := by
  have h := sum_primeKloostermanTrace_joint_moment S (fun _ => 1)
  simp only [pow_one, sum_primeKloostermanTrace] at h
  rw [h]
  by_cases hS : S = ∅
  · simp [hS]
  · rw [if_neg hS]
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact prod_eq_zero_iff.mpr ⟨p, hp, rfl⟩

/-- The exact complete joint second moment includes a factor `p-1` at each prime. -/
theorem sum_primeKloostermanTrace_prod_sq (S : Finset Nat.Primes) :
    (∑ n ∈ range (primeSetProduct S),
      (∏ p ∈ S, primeKloostermanTrace p (n : ZMod p.val)) ^ 2) =
      (primeSetProduct S : ℝ) * ∏ p ∈ S, ((p.val : ℝ) - 1) := by
  simp only [← prod_pow]
  rw [sum_primeKloostermanTrace_joint_moment]
  simp only [sum_primeKloostermanTrace_sq, prod_mul_distrib, primeSetProduct, Nat.cast_prod]

/-- Normalizing each trace by `√p` leaves the exact product `∏(1-1/p)`. -/
theorem mean_primeKloostermanTrace_normalized_prod_sq (S : Finset Nat.Primes) :
    (∑ n ∈ range (primeSetProduct S),
      ∏ p ∈ S, (primeKloostermanTrace p (n : ZMod p.val) ^ 2 / (p.val : ℝ))) /
        (primeSetProduct S : ℝ) = ∏ p ∈ S, (1 - 1 / (p.val : ℝ)) := by
  simp only [prod_div_distrib, prod_pow, ← sum_div]
  rw [sum_primeKloostermanTrace_prod_sq]
  have hP : (primeSetProduct S : ℝ) ≠ 0 := by
    exact_mod_cast (primeSetProduct_pos S).ne'
  rw [← Nat.cast_prod]
  change ((primeSetProduct S : ℝ) * _ / (primeSetProduct S : ℝ)) /
    (primeSetProduct S : ℝ) = _
  rw [mul_div_cancel_left₀ _ hP]
  rw [primeSetProduct, Nat.cast_prod]
  rw [← prod_div_distrib]
  apply prod_congr rfl
  intro p _
  have hp : (p.val : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  field_simp

private theorem sum_primeField_nonzero (p : Nat.Primes) (f : ZMod p.val → ℝ) :
    (∑ a : ZMod p.val, if a = 0 then 0 else f a) =
      ∑ a ∈ (univ : Finset (ZMod p.val)).erase 0, f a := by
  rw [← sum_erase_add (univ : Finset (ZMod p.val))
    (fun a => if a = 0 then 0 else f a) (mem_univ 0)]
  simp only [ite_true, add_zero]
  apply sum_congr rfl
  intro a ha
  exact if_neg (mem_erase.mp ha).1

/-- Excluding the singular residue at every prime still gives exact local factorization. -/
theorem sum_primeKloostermanTrace_joint_nonzero_moment (S : Finset Nat.Primes)
    (r : Nat.Primes → ℕ) :
    (∑ n ∈ range (primeSetProduct S),
      ∏ p ∈ S, if (n : ZMod p.val) = 0 then 0 else
        primeKloostermanTrace p (n : ZMod p.val) ^ r p) =
      ∏ p ∈ S, ∑ a ∈ (univ : Finset (ZMod p.val)).erase 0,
        primeKloostermanTrace p a ^ r p := by
  rw [sum_range_primeSetProduct_prod S _
    (fun p => primeResidue_local_periodic p
      (fun a => if a = 0 then 0 else primeKloostermanTrace p a ^ r p))]
  apply prod_congr rfl
  intro p _
  exact (RHTower.Sieve.sum_zmod_eq_sum_range_natCast p.val
    (fun a : ZMod p.val => if a = 0 then 0 else primeKloostermanTrace p a ^ r p)).symm.trans
      (sum_primeField_nonzero p (fun a => primeKloostermanTrace p a ^ r p))

/-- The punctured joint trace has total one, at every finite prime set. -/
theorem sum_primeKloostermanTrace_nonzero_prod (S : Finset Nat.Primes) :
    (∑ n ∈ range (primeSetProduct S),
      ∏ p ∈ S, if (n : ZMod p.val) = 0 then 0 else
        primeKloostermanTrace p (n : ZMod p.val)) = 1 := by
  have h := sum_primeKloostermanTrace_joint_nonzero_moment S (fun _ => 1)
  simpa only [pow_one, sum_primeKloostermanTrace_ne_zero, prod_const_one] using h

/-- Punctured joint energy is the product of the exact local energies. -/
theorem sum_primeKloostermanTrace_nonzero_prod_sq (S : Finset Nat.Primes) :
    (∑ n ∈ range (primeSetProduct S),
      ∏ p ∈ S, if (n : ZMod p.val) = 0 then 0 else
        primeKloostermanTrace p (n : ZMod p.val) ^ 2) =
      ∏ p ∈ S, ((p.val : ℝ) ^ 2 - p.val - 1) := by
  rw [sum_primeKloostermanTrace_joint_nonzero_moment]
  simp only [sum_primeKloostermanTrace_sq_ne_zero]

#print axioms sum_primeKloostermanTrace_joint_moment
#print axioms sum_primeKloostermanTrace_prod
#print axioms mean_primeKloostermanTrace_normalized_prod_sq
#print axioms sum_primeKloostermanTrace_joint_nonzero_moment
#print axioms sum_primeKloostermanTrace_nonzero_prod_sq

end

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
