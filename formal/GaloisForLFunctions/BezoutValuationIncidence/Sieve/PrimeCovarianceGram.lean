import GaloisForLFunctions.BezoutValuationIncidence.Sieve.WeightedResidueCovariance

/-!
# Finite Gram sums of centered prime residues

Pairwise covariance retains the exact equal-prime collision mean. Summing
its Abel errors costs the square of the absolute coefficient mass, with
one inverse receiving endpoint.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- The exact period mean of two centered prime residue indicators. -/
def primeResidueMean (p q a b : ℕ) : ℝ :=
  if p = q then (if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2 else 0

theorem weighted_prime_covariance {f g : ℕ → ℝ} {M K : ℝ}
    (hM : 0 ≤ M) {A B p q a b : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hp : p.Prime) (hq : q.Prime)
    (hf : ∀ n ∈ Icc A B, |f n| ≤ M) (hg : ∀ n ∈ Icc A B, |g n| ≤ M)
    (hfv : discreteVariation f A B ≤ K) (hgv : discreteVariation g A B ≤ K) :
    |∑ n ∈ Icc A B, (centeredResidue p a n * centeredResidue q b n -
      primeResidueMean p q a b) * (f n * g n / (n : ℝ))| ≤
        3 * (2 * M ^ 2 + 2 * M * K) / (A : ℝ) := by
  by_cases he : p = q
  · subst q
    simpa only [primeResidueMean, if_true] using
      weighted_same_covariance hM hA hAB hp.pos hf hg hfv hgv
  · simpa only [primeResidueMean, if_neg he, sub_zero] using
      weighted_coprime_covariance hM hA hAB hp.pos hq.pos
        ((Nat.coprime_primes hp hq).mpr he) hf hg hfv hgv

/-- Pairwise covariance errors sum with the square of the absolute coefficient mass. -/
theorem finite_covariance_Gram {α : Type*} (I : Finset α)
    (x f : α → ℕ → ℝ) (μ : α → α → ℝ) (w : α → ℝ) {C : ℝ} {A B : ℕ}
    (hpair : ∀ i ∈ I, ∀ j ∈ I,
      |∑ n ∈ Icc A B, (x i n * x j n - μ i j) * (f i n * f j n / (n : ℝ))| ≤ C) :
    |(∑ n ∈ Icc A B, (∑ i ∈ I, w i * f i n * x i n) ^ 2 / (n : ℝ)) -
      ∑ i ∈ I, ∑ j ∈ I, w i * w j * μ i j *
        ∑ n ∈ Icc A B, f i n * f j n / (n : ℝ)| ≤
      C * (∑ i ∈ I, |w i|) ^ 2 := by
  classical
  let E : α → α → ℝ := fun i j =>
    ∑ n ∈ Icc A B, (x i n * x j n -
      μ i j) * (f i n * f j n / (n : ℝ))
  have hE (i : α) (hi : i ∈ I) (j : α) (hj : j ∈ I) : |E i j| ≤ C :=
    hpair i hi j hj
  have hexpand (n : ℕ) :
      (∑ i ∈ I, w i * f i n * x i n) ^ 2 / (n : ℝ) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j *
          (x i n * x j n) *
            (f i n * f j n / (n : ℝ)) := by
    rw [pow_two, sum_mul_sum, sum_div]
    apply sum_congr rfl
    intro i _
    rw [sum_div]
    apply sum_congr rfl
    intro j _
    ring
  have hid :
      (∑ n ∈ Icc A B, (∑ i ∈ I, w i * f i n * x i n) ^ 2 / (n : ℝ)) -
        (∑ i ∈ I, ∑ j ∈ I, w i * w j * μ i j *
          ∑ n ∈ Icc A B, f i n * f j n / (n : ℝ)) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * E i j := by
    simp_rw [hexpand]
    rw [sum_comm]
    simp_rw [sum_comm (s := Icc A B) (t := I)]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    simp only [E, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [hid]
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, |w i * w j * E i j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, |w i| * |w j| * C := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hE i hi j hj) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      rw [pow_two, sum_mul_sum]
      simp only [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring

/-- Finite coherent sums have the exact prime-covariance main term and an inverse-endpoint error. -/
theorem prime_covariance_Gram {α : Type*} (I : Finset α)
    (p a : α → ℕ) (w : α → ℝ) (f : α → ℕ → ℝ) {M K : ℝ}
    (hM : 0 ≤ M) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hp : ∀ i ∈ I, (p i).Prime)
    (hf : ∀ i ∈ I, ∀ n ∈ Icc A B, |f i n| ≤ M)
    (hfv : ∀ i ∈ I, discreteVariation (f i) A B ≤ K) :
    |(∑ n ∈ Icc A B, (∑ i ∈ I, w i * f i n * centeredResidue (p i) (a i) n) ^ 2 / (n : ℝ)) -
      ∑ i ∈ I, ∑ j ∈ I, w i * w j * primeResidueMean (p i) (p j) (a i) (a j) *
        ∑ n ∈ Icc A B, f i n * f j n / (n : ℝ)| ≤
      (3 * (2 * M ^ 2 + 2 * M * K) / (A : ℝ)) * (∑ i ∈ I, |w i|) ^ 2 := by
  apply finite_covariance_Gram
  intro i hi j hj
  exact weighted_prime_covariance hM hA hAB (hp i hi) (hp j hj)
    (hf i hi) (hf j hj) (hfv i hi) (hfv j hj)

#print axioms finite_covariance_Gram
#print axioms prime_covariance_Gram

end GaloisForLFunctions.BezoutValuationIncidence
