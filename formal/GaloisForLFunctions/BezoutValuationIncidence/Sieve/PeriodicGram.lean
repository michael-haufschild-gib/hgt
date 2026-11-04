import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PeriodicWeightedCovariance

/-!
# Periodic prime covariance in finite Gram sums

The exact conductor correlation multiplies each prime collision mean.
The finite-period error costs the squared absolute multiplier mass.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- The exact covariance mean retains the cross-correlation of the fixed periodic factors. -/
def periodicPrimeResidueMean (M p q a b : ℕ) (z w : ℕ → ℝ) : ℝ :=
  primeResidueMean p q a b * ((∑ r ∈ range M, z r * w r) / M)

/-- Fixed periodic receiving fibres preserve the inverse-endpoint finite Gram error. -/
theorem periodic_prime_covariance_Gram {α : Type*} (I : Finset α)
    (p a : α → ℕ) (w : α → ℝ) (z f : α → ℕ → ℝ) {U K V : ℝ}
    (hU : 0 ≤ U) (hK : 0 ≤ K) (hV : 0 ≤ V)
    {A B M : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hM : 0 < M)
    (hp : ∀ i ∈ I, (p i).Prime) (hMp : ∀ i ∈ I, M.Coprime (p i))
    (hz : ∀ i ∈ I, ∀ r ∈ range M, |z i r| ≤ V)
    (hf : ∀ i ∈ I, ∀ n ∈ Icc A B, |f i n| ≤ U)
    (hfv : ∀ i ∈ I, discreteVariation (f i) A B ≤ K) :
    |(∑ n ∈ Icc A B,
        (∑ i ∈ I, w i * f i n * (z i (n % M) * centeredResidue (p i) (a i) n)) ^ 2 / (n : ℝ)) -
      ∑ i ∈ I, ∑ j ∈ I, w i * w j *
        periodicPrimeResidueMean M (p i) (p j) (a i) (a j) (z i) (z j) *
          ∑ n ∈ Icc A B, f i n * f j n / (n : ℝ)| ≤
      (4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A) *
        (∑ i ∈ I, |w i|) ^ 2 := by
  apply finite_covariance_Gram
  intro i hi j hj
  have h := weighted_periodic_prime_covariance (a := a i) (b := a j) hU hA hAB hM (hp i hi) (hp j hj)
    (hMp i hi) (hMp j hj) (fun r => z i r * z j r)
      (hf i hi) (hf j hj) (hfv i hi) (hfv j hj)
  have hmass : (∑ r ∈ range M, |z i r * z j r|) ≤ (M : ℝ) * V ^ 2 := by
    calc
      _ ≤ ∑ r ∈ range M, V ^ 2 := by
        apply sum_le_sum
        intro r hr
        rw [abs_mul, pow_two]
        exact mul_le_mul (hz i hi r hr) (hz j hj r hr) (abs_nonneg _) hV
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have hcost : 0 ≤ 2 * U ^ 2 + 2 * U * K := by positivity
  have hbound :
      (4 * ∑ r ∈ range M, |z i r * z j r|) * (2 * U ^ 2 + 2 * U * K) / A ≤
        4 * (M : ℝ) * V ^ 2 * (2 * U ^ 2 + 2 * U * K) / A := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg A)
    apply mul_le_mul_of_nonneg_right _ hcost
    exact (mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)
  have he :
      (∑ n ∈ Icc A B,
        ((z i (n % M) * centeredResidue (p i) (a i) n) *
          (z j (n % M) * centeredResidue (p j) (a j) n) -
            periodicPrimeResidueMean M (p i) (p j) (a i) (a j) (z i) (z j)) *
              (f i n * f j n / (n : ℝ))) =
      ∑ n ∈ Icc A B,
        ((z i (n % M) * z j (n % M)) * centeredResidue (p i) (a i) n * centeredResidue (p j) (a j) n -
          primeResidueMean (p i) (p j) (a i) (a j) * ((∑ r ∈ range M, z i r * z j r) / M)) *
            (f i n * f j n / (n : ℝ)) := by
    apply sum_congr rfl
    intro n _
    dsimp only [periodicPrimeResidueMean]
    ring
  rw [he]
  exact h.trans hbound

#print axioms periodic_prime_covariance_Gram

end GaloisForLFunctions.BezoutValuationIncidence
