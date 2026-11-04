import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PeriodicGram
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.CollisionMass

/-!
# Collision control of periodic prime Gram blocks

Different source primes have zero period mean. Within one prime block,
the exact periodic correlation is bounded by its square amplitude, and an
affine collision-row bound supplies the second reciprocal prime factor.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- The absolute period correlation is bounded by the product of uniform amplitudes. -/
theorem abs_period_mean_product_le {M : ℕ} (hM : 0 < M) (z w : ℕ → ℝ)
    {V : ℝ} (hV : 0 ≤ V) (hz : ∀ r ∈ range M, |z r| ≤ V)
    (hw : ∀ r ∈ range M, |w r| ≤ V) :
    |(∑ r ∈ range M, z r * w r) / (M : ℝ)| ≤ V ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rw [abs_div, abs_of_pos hM0]
  apply (div_le_iff₀ hM0).mpr
  calc
    _ ≤ ∑ r ∈ range M, |z r * w r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ range M, V ^ 2 := by
      apply sum_le_sum
      intro r hr
      rw [abs_mul, pow_two]
      exact mul_le_mul (hz r hr) (hw r hr) (abs_nonneg _) hV
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]

/-- Positive collision rows bound the entire periodic covariance main term. -/
theorem periodic_prime_block_main_le {α : Type*} (P : Finset ℕ) (I : Finset α)
    {M : ℕ} (hM : 0 < M) (a : ℕ → α → ℕ) (z : ℕ → α → ℕ → ℝ)
    (v : ℕ → α → ℝ) {V : ℝ} (hV : 0 ≤ V) (D C E : ℕ → ℝ)
    (hp : ∀ p ∈ P, 0 < p)
    (hz : ∀ p ∈ P, ∀ i ∈ I, ∀ r ∈ range M, |z p i r| ≤ V)
    (hv : ∀ p ∈ P, ∀ i ∈ I, 0 ≤ v p i)
    (hC : ∀ p ∈ P, 0 ≤ C p) (hE : ∀ p ∈ P, 0 ≤ E p)
    (htotal : ∀ p ∈ P, (∑ i ∈ I, v p i) ≤ D p)
    (hrow : ∀ p ∈ P, ∀ j ∈ I,
      (∑ i ∈ I, if a p i ≡ a p j [MOD p] then v p i else 0) ≤ C p / p + E p) :
    (∑ p ∈ P, ∑ i ∈ I, ∑ j ∈ I,
      v p i * v p j * periodicPrimeResidueMean M p p (a p i) (a p j) (z p i) (z p j)) ≤
      V ^ 2 * (∑ p ∈ P, (D p * (C p + D p) / (p : ℝ) ^ 2 + D p * E p / p)) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hpP
  have hmain := same_prime_quadratic_mass I (v p) (a p) (hp p hpP)
    (hC p hpP) (hE p hpP) (hv p hpP) (htotal p hpP) (hrow p hpP)
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I,
        v p i * v p j *
          |(if a p i ≡ a p j [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2| * V ^ 2 := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hmean := abs_period_mean_product_le hM (z p i) (z p j) hV
        (hz p hpP i hi) (hz p hpP j hj)
      have hμ : periodicPrimeResidueMean M p p (a p i) (a p j) (z p i) (z p j) ≤
          |(if a p i ≡ a p j [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2| * V ^ 2 := by
        unfold periodicPrimeResidueMean primeResidueMean
        rw [if_pos rfl]
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hmean (abs_nonneg _))
      exact (mul_le_mul_of_nonneg_left hμ
        (mul_nonneg (hv p hpP i hi) (hv p hpP j hj))).trans_eq (by ring)
    _ = V ^ 2 * (∑ i ∈ I, ∑ j ∈ I, v p i * v p j *
        |(if a p i ≡ a p j [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2|) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (sq_nonneg V)

/-- The covariance mean decomposes exactly into equal-prime blocks before receiving-row summation. -/
theorem periodic_prime_Gram_main_eq_blocks {α : Type*} (P : Finset ℕ) (I : Finset α)
    (M A B : ℕ) (a : ℕ → α → ℕ) (w : ℕ → α → ℝ)
    (z f : ℕ → α → ℕ → ℝ) :
    (∑ i ∈ P ×ˢ I, ∑ j ∈ P ×ˢ I, w i.1 i.2 * w j.1 j.2 *
      periodicPrimeResidueMean M i.1 j.1 (a i.1 i.2) (a j.1 j.2) (z i.1 i.2) (z j.1 j.2) *
        ∑ n ∈ Icc A B, f i.1 i.2 n * f j.1 j.2 n / (n : ℝ)) =
      ∑ n ∈ Icc A B, (∑ p ∈ P, ∑ i ∈ I, ∑ j ∈ I,
        (w p i * f p i n) * (w p j * f p j n) *
          periodicPrimeResidueMean M p p (a p i) (a p j) (z p i) (z p j)) / (n : ℝ) := by
  classical
  have hblock :
      (∑ i ∈ P ×ˢ I, ∑ j ∈ P ×ˢ I, w i.1 i.2 * w j.1 j.2 *
        periodicPrimeResidueMean M i.1 j.1 (a i.1 i.2) (a j.1 j.2) (z i.1 i.2) (z j.1 j.2) *
          ∑ n ∈ Icc A B, f i.1 i.2 n * f j.1 j.2 n / (n : ℝ)) =
      ∑ p ∈ P, ∑ i ∈ I, ∑ j ∈ I, w p i * w p j *
        periodicPrimeResidueMean M p p (a p i) (a p j) (z p i) (z p j) *
          ∑ n ∈ Icc A B, f p i n * f p j n / (n : ℝ) := by
    simp only [sum_product]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro i _
    apply sum_eq_single p
    · intro q _ hqp
      apply sum_eq_zero
      intro j _
      simp only [periodicPrimeResidueMean, primeResidueMean, if_neg (Ne.symm hqp),
        zero_mul, mul_zero]
    · intro h
      exact False.elim (h hp)
  rw [hblock]
  simp only [mul_sum, sum_div]
  have hterm (p : ℕ) (i j : α) (n : ℕ) :
      w p i * w p j * periodicPrimeResidueMean M p p (a p i) (a p j) (z p i) (z p j) *
          (f p i n * f p j n / (n : ℝ)) =
        ((w p i * f p i n) * (w p j * f p j n) *
          periodicPrimeResidueMean M p p (a p i) (a p j) (z p i) (z p j)) / (n : ℝ) := by ring
  simp_rw [hterm]
  simp_rw [sum_comm (s := I) (t := Icc A B)]
  rw [sum_comm (s := P) (t := Icc A B)]

/-- Collision-row control and bounded variation give the full finite periodic Gram bound. -/
theorem periodic_prime_block_Gram_le {α : Type*} (P : Finset ℕ) (I : Finset α)
    (a : ℕ → α → ℕ) (w : ℕ → α → ℝ) (z f : ℕ → α → ℕ → ℝ)
    {U K V : ℝ} (hU : 0 ≤ U) (hK : 0 ≤ K) (hV : 0 ≤ V)
    {A B M : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hM : 0 < M)
    (hp : ∀ p ∈ P, p.Prime) (hMp : ∀ p ∈ P, M.Coprime p)
    (hw : ∀ p ∈ P, ∀ i ∈ I, 0 ≤ w p i)
    (hz : ∀ p ∈ P, ∀ i ∈ I, ∀ r ∈ range M, |z p i r| ≤ V)
    (hf0 : ∀ p ∈ P, ∀ i ∈ I, ∀ n ∈ Icc A B, 0 ≤ f p i n)
    (hf : ∀ p ∈ P, ∀ i ∈ I, ∀ n ∈ Icc A B, |f p i n| ≤ U)
    (hfv : ∀ p ∈ P, ∀ i ∈ I, discreteVariation (f p i) A B ≤ K)
    (D C E : ℕ → ℕ → ℝ)
    (hC : ∀ n ∈ Icc A B, ∀ p ∈ P, 0 ≤ C n p)
    (hE : ∀ n ∈ Icc A B, ∀ p ∈ P, 0 ≤ E n p)
    (htotal : ∀ n ∈ Icc A B, ∀ p ∈ P, (∑ i ∈ I, w p i * f p i n) ≤ D n p)
    (hrow : ∀ n ∈ Icc A B, ∀ p ∈ P, ∀ j ∈ I,
      (∑ i ∈ I, if a p i ≡ a p j [MOD p] then w p i * f p i n else 0) ≤
        C n p / p + E n p) :
    (∑ n ∈ Icc A B, (∑ i ∈ P ×ˢ I,
        w i.1 i.2 * f i.1 i.2 n *
          (z i.1 i.2 (n % M) * centeredResidue i.1 (a i.1 i.2) n)) ^ 2 / (n : ℝ)) ≤
      V ^ 2 * (∑ n ∈ Icc A B,
        (∑ p ∈ P, (D n p * (C n p + D n p) / (p : ℝ) ^ 2 + D n p * E n p / p)) / (n : ℝ)) +
      (4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A) *
        (∑ i ∈ P ×ˢ I, |w i.1 i.2|) ^ 2 := by
  classical
  have h := periodic_prime_covariance_Gram (P ×ˢ I) Prod.fst
    (fun i => a i.1 i.2) (fun i => w i.1 i.2)
    (fun i => z i.1 i.2) (fun i => f i.1 i.2) hU hK hV hA hAB hM
    (fun i hi => hp i.1 (mem_product.mp hi).1)
    (fun i hi => hMp i.1 (mem_product.mp hi).1)
    (fun i hi => hz i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun i hi => hf i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
    (fun i hi => hfv i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2)
  have hupper := (abs_le.mp h).2
  rw [periodic_prime_Gram_main_eq_blocks] at hupper
  have hmain :
      (∑ n ∈ Icc A B, (∑ p ∈ P, ∑ i ∈ I, ∑ j ∈ I,
        (w p i * f p i n) * (w p j * f p j n) *
          periodicPrimeResidueMean M p p (a p i) (a p j) (z p i) (z p j)) / (n : ℝ)) ≤
      V ^ 2 * (∑ n ∈ Icc A B,
        (∑ p ∈ P, (D n p * (C n p + D n p) / (p : ℝ) ^ 2 + D n p * E n p / p)) / (n : ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hm := periodic_prime_block_main_le P I hM a z (fun p i => w p i * f p i n)
      hV (D n) (C n) (E n) (fun p hpP => (hp p hpP).pos) hz
      (fun p hpP i hi => mul_nonneg (hw p hpP i hi) (hf0 p hpP i hi n hn))
      (hC n hn) (hE n hn) (htotal n hn) (hrow n hn)
    exact (div_le_div_of_nonneg_right hm (Nat.cast_nonneg n)).trans_eq (by ring)
  linarith only [hupper, hmain]

#print axioms periodic_prime_block_Gram_le

#print axioms periodic_prime_block_main_le
#print axioms periodic_prime_Gram_main_eq_blocks

end GaloisForLFunctions.BezoutValuationIncidence
