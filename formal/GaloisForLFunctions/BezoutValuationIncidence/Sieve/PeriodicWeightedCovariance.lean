import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PeriodicCovariance
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PrimeCovarianceGram

/-!
# Weighted prime covariance with periodic factors

Abel summation keeps the exact periodic covariance mean. Uniform kernel
variation leaves an error inversely proportional to the receiving endpoint.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence

private theorem periodic_Icc_eq_Ioc_pred {A B : ℕ} (hA : 1 ≤ A) :
    Icc A B = Ioc (A - 1) B := by
  ext n
  simp only [mem_Icc, mem_Ioc]
  omega

private theorem periodic_inverse_bound {p : ℕ} (hp : 0 < p) :
    1 + 1 / (p : ℝ) ≤ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hi := one_div_le_one_div_of_le (zero_lt_one : (0 : ℝ) < 1) hp1
  norm_num only [one_div_one] at hi
  linarith only [hi]

/-- A coprime periodic factor changes the covariance mean by its period average only. -/
theorem periodic_prime_covariance_Icc {A B M p q a b : ℕ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (hM : 0 < M) (hp : p.Prime) (hq : q.Prime)
    (hMp : M.Coprime p) (hMq : M.Coprime q) (z : ℕ → ℝ) :
    |∑ n ∈ Icc A B,
      (z (n % M) * centeredResidue p a n * centeredResidue q b n -
        primeResidueMean p q a b * ((∑ r ∈ range M, z r) / M))| ≤
      4 * ∑ r ∈ range M, |z r| := by
  have hmass : 0 ≤ ∑ r ∈ range M, |z r| := sum_nonneg fun r _ => abs_nonneg _
  by_cases he : p = q
  · subst q
    rw [periodic_Icc_eq_Ioc_pred hA, sum_sub_distrib, sum_const, nsmul_eq_mul,
      Nat.card_Ioc, Nat.cast_sub (by omega : A - 1 ≤ B)]
    have h := periodic_same_covariance (A := A - 1) (B := B) (a := a) (b := b)
      (by omega) hM hp.pos hMp z
    have hfac : (1 + 1 / (p : ℝ)) ^ 2 ≤ 4 := by
      have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 1 / (p : ℝ))
        (periodic_inverse_bound hp.pos) 2
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at h
      exact h
    simpa only [primeResidueMean, if_true, mul_assoc] using
      h.trans (mul_le_mul_of_nonneg_right hfac hmass)
  · simp only [primeResidueMean, if_neg he, zero_mul, sub_zero]
    rw [periodic_Icc_eq_Ioc_pred hA]
    have h := periodic_coprime_covariance (A := A - 1) (B := B) (a := a) (b := b)
      (by omega) hM hp.pos hq.pos hMp hMq ((Nat.coprime_primes hp hq).mpr he) z
    have hfac : (1 + 1 / (p : ℝ)) * (1 + 1 / (q : ℝ)) ≤ 4 := by
      have h := mul_le_mul (periodic_inverse_bound hp.pos) (periodic_inverse_bound hq.pos)
        (by positivity : 0 ≤ 1 + 1 / (q : ℝ)) zero_le_two
      norm_num only [show (2 : ℝ) * 2 = 4 by norm_num] at h
      exact h
    exact h.trans (mul_le_mul_of_nonneg_right hfac hmass)

/-- Abel summation retains the exact periodic prime-covariance mean through literal kernel weights. -/
theorem weighted_periodic_prime_covariance {f g : ℕ → ℝ} {U K : ℝ}
    (hU : 0 ≤ U) {A B M p q a b : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hM : 0 < M) (hp : p.Prime) (hq : q.Prime) (hMp : M.Coprime p) (hMq : M.Coprime q)
    (z : ℕ → ℝ) (hf : ∀ n ∈ Icc A B, |f n| ≤ U) (hg : ∀ n ∈ Icc A B, |g n| ≤ U)
    (hfv : discreteVariation f A B ≤ K) (hgv : discreteVariation g A B ≤ K) :
    |∑ n ∈ Icc A B,
      (z (n % M) * centeredResidue p a n * centeredResidue q b n -
        primeResidueMean p q a b * ((∑ r ∈ range M, z r) / M)) *
          (f n * g n / (n : ℝ))| ≤
      (4 * ∑ r ∈ range M, |z r|) * (2 * U ^ 2 + 2 * U * K) / A := by
  have hpref : ∀ m, A ≤ m → m ≤ B →
      |∑ n ∈ Icc A m,
        (z (n % M) * centeredResidue p a n * centeredResidue q b n -
          primeResidueMean p q a b * ((∑ r ∈ range M, z r) / M))| ≤
        4 * ∑ r ∈ range M, |z r| :=
    fun m hm _ => periodic_prime_covariance_Icc hA hm hM hp hq hMp hMq z
  have h := abs_weighted_sum_le_of_prefix (w := fun n => f n * g n / (n : ℝ)) hAB hpref
  have hk := pair_kernel_variation hU hA hAB hf hg hfv hgv
  refine h.trans ?_
  exact (mul_le_mul_of_nonneg_left hk
    (mul_nonneg (by norm_num) (sum_nonneg fun r _ => abs_nonneg (z r)))).trans_eq (by ring)

#print axioms periodic_prime_covariance_Icc
#print axioms weighted_periodic_prime_covariance

end GaloisForLFunctions.BezoutValuationIncidence
