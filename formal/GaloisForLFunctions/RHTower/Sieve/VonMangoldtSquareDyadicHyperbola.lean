/- Exact dyadic block squeeze for the harmonic convolution of the Mangoldt square. -/

import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSquareDyadicProfile
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSquareHyperbola
import GaloisForLFunctions.HTGeometry.IocPartitionSum

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction BigOperators

namespace RHTower.Sieve

private def vonMangoldtSquareHarmonicWeight (n : ℕ) : ℝ :=
  (Λ n) ^ (2 : ℕ) / (n : ℝ)

private theorem vonMangoldtSquareHarmonicWeight_nonneg (n : ℕ) :
    0 ≤ vonMangoldtSquareHarmonicWeight n := by
  unfold vonMangoldtSquareHarmonicWeight
  positivity

private theorem sum_Ioc_vonMangoldtSquareHarmonicWeight_eq_sub
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc a b, vonMangoldtSquareHarmonicWeight n) =
      vonMangoldtHarmonicSquareSum b - vonMangoldtHarmonicSquareSum a := by
  rw [vonMangoldtHarmonicSquareSum_eq_Icc_one b (ha.trans hab),
    vonMangoldtHarmonicSquareSum_eq_Icc_one a ha]
  have hunion : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_Ioc] at hn'
    omega
  rw [hunion, Finset.sum_union hdisj]
  unfold vonMangoldtSquareHarmonicWeight
  ring

private theorem pow_two_sub_mul_pow_two_eq {M k : ℕ} (hk : k ≤ M) :
    2 ^ k * 2 ^ (M - k) = 2 ^ M := by
  rw [← pow_add]
  congr 1
  omega

private theorem dyadic_lower_div_cutoff {M k d : ℕ}
    (hk : k < M) (hdpos : 0 < d) (hd : d ≤ 2 ^ (M - k)) :
    2 ^ k ≤ 2 ^ M / d := by
  apply (Nat.le_div_iff_mul_le hdpos).mpr
  calc
    2 ^ k * d ≤ 2 ^ k * 2 ^ (M - k) := Nat.mul_le_mul_left _ hd
    _ = 2 ^ M := pow_two_sub_mul_pow_two_eq (Nat.le_of_lt hk)

private theorem dyadic_upper_div_cutoff {M k d : ℕ}
    (hk : k < M) (hdlo : 2 ^ (M - (k + 1)) < d) :
    2 ^ M / d ≤ 2 ^ (k + 1) := by
  by_contra hnot
  have hdiv : 2 ^ (k + 1) < 2 ^ M / d := by omega
  have hmul1 : 2 ^ (M - (k + 1)) * 2 ^ (k + 1) <
      2 ^ (M - (k + 1)) * (2 ^ M / d) :=
    Nat.mul_lt_mul_of_pos_left hdiv (by positivity)
  have hmul2 : 2 ^ (M - (k + 1)) * (2 ^ M / d) ≤
      d * (2 ^ M / d) := Nat.mul_le_mul_right _ (Nat.le_of_lt hdlo)
  have hmul := hmul1.trans_le hmul2
  have hpow : 2 ^ (M - (k + 1)) * 2 ^ (k + 1) = 2 ^ M := by
    rw [← pow_add]
    congr 1
    omega
  have hle : d * (2 ^ M / d) ≤ 2 ^ M := Nat.mul_div_le _ _
  rw [hpow] at hmul
  omega

private theorem vonMangoldtSquareHyperbolaMass_eq_dyadic_blocks (M : ℕ) :
    vonMangoldtSquareHyperbolaMass (2 ^ M) =
      ∑ k ∈ Finset.range M,
        ∑ d ∈ Finset.Ioc (2 ^ (M - (k + 1))) (2 ^ (M - k)),
          vonMangoldtSquareHarmonicWeight d *
            vonMangoldtHarmonicSquareSum (2 ^ M / d) := by
  let f : ℕ → ℝ := fun d => vonMangoldtSquareHarmonicWeight d *
    vonMangoldtHarmonicSquareSum (2 ^ M / d)
  have hform : vonMangoldtSquareHyperbolaMass (2 ^ M) =
      ∑ d ∈ Finset.Ioc 1 (2 ^ M), f d := by
    rw [vonMangoldtSquareHyperbolaMass]
    have hterm : ∀ d ∈ Finset.Icc 1 (2 ^ M),
        (Λ d) ^ (2 : ℕ) / (d : ℝ) *
            ∑ m ∈ Finset.Icc 1 (2 ^ M / d), (Λ m) ^ (2 : ℕ) / (m : ℝ) =
          f d := by
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdle : d ≤ 2 ^ M := (Finset.mem_Icc.mp hd).2
      have hdiv : 1 ≤ 2 ^ M / d := by
        apply (Nat.le_div_iff_mul_le hdpos).mpr
        simpa using hdle
      rw [← vonMangoldtHarmonicSquareSum_eq_Icc_one (2 ^ M / d) hdiv]
      rfl
    rw [Finset.sum_congr rfl hterm]
    have hset : Finset.Icc 1 (2 ^ M) = insert 1 (Finset.Ioc 1 (2 ^ M)) := by
      have hpowone : 1 ≤ 2 ^ M := one_le_pow₀ (by norm_num : 1 ≤ 2)
      ext d
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp [f, vonMangoldtSquareHarmonicWeight]
  let cut : ℕ → ℕ := fun k => 2 ^ (M - k)
  have hanti : ∀ k, k < M → cut (k + 1) ≤ cut k := by
    intro k hk
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hpart := HTGeometry.sum_Ioc_partition f cut M hanti
  rw [hform]
  simpa [cut, f] using hpart.symm

/-- Dyadic multiplicative hyperbola is squeezed by adjacent increment convolutions. -/
theorem quadraticIncrementConvolution_pred_le_vonMangoldtSquareHyperbolaMass_pow_two
    (M : ℕ) :
    quadraticIncrementConvolution vonMangoldtSquareDyadicProfile (M - 1) ≤
      vonMangoldtSquareHyperbolaMass (2 ^ M) := by
  by_cases hM0 : M = 0
  · subst M
    norm_num [quadraticIncrementConvolution, vonMangoldtSquareHyperbolaMass,
      vonMangoldtSquare, vonMangoldtSquareDyadicProfile]
  rw [vonMangoldtSquareHyperbolaMass_eq_dyadic_blocks]
  have hblock : ∀ k ∈ Finset.range M,
      (vonMangoldtSquareDyadicProfile (M - k) -
          vonMangoldtSquareDyadicProfile (M - (k + 1))) *
          vonMangoldtSquareDyadicProfile k ≤
        ∑ d ∈ Finset.Ioc (2 ^ (M - (k + 1))) (2 ^ (M - k)),
          vonMangoldtSquareHarmonicWeight d *
            vonMangoldtHarmonicSquareSum (2 ^ M / d) := by
    intro k hk
    have hkM : k < M := Finset.mem_range.mp hk
    change (vonMangoldtHarmonicSquareSum (2 ^ (M - k)) -
        vonMangoldtHarmonicSquareSum (2 ^ (M - (k + 1)))) *
        vonMangoldtHarmonicSquareSum (2 ^ k) ≤ _
    have hlo1 : 1 ≤ 2 ^ (M - (k + 1)) := one_le_pow₀ (by norm_num)
    have hlohi : 2 ^ (M - (k + 1)) ≤ 2 ^ (M - k) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    rw [← sum_Ioc_vonMangoldtSquareHarmonicWeight_eq_sub hlo1 hlohi]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d hd
    have hdhi : d ≤ 2 ^ (M - k) := (Finset.mem_Ioc.mp hd).2
    have hdpos : 0 < d := lt_of_lt_of_le (by positivity)
      (Nat.le_of_lt (Finset.mem_Ioc.mp hd).1)
    have hcut := dyadic_lower_div_cutoff hkM hdpos hdhi
    exact mul_le_mul_of_nonneg_left
      (monotone_vonMangoldtHarmonicSquareSum hcut)
      (vonMangoldtSquareHarmonicWeight_nonneg d)
  have hsum := Finset.sum_le_sum hblock
  refine le_trans ?_ hsum
  rw [quadraticIncrementConvolution]
  have hreflect := Finset.sum_range_reflect
    (fun j => (vonMangoldtSquareDyadicProfile (j + 1) -
      vonMangoldtSquareDyadicProfile j) *
      vonMangoldtSquareDyadicProfile (M - 1 - j)) M
  have hrev :
      (∑ k ∈ Finset.range M,
        (vonMangoldtSquareDyadicProfile (M - k) -
          vonMangoldtSquareDyadicProfile (M - (k + 1))) *
          vonMangoldtSquareDyadicProfile k) =
      ∑ j ∈ Finset.range M,
        (vonMangoldtSquareDyadicProfile (j + 1) -
          vonMangoldtSquareDyadicProfile j) *
          vonMangoldtSquareDyadicProfile (M - 1 - j) := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k < M := Finset.mem_range.mp hk
    have h1 : M - 1 - k + 1 = M - k := by omega
    have h2 : M - 1 - k = M - (k + 1) := by omega
    have h3 : M - 1 - (M - (k + 1)) = k := by omega
    rw [h1, h2, h3]
  rw [hrev]
  rw [show M = (M - 1) + 1 by omega]
  rw [Finset.sum_range_succ]
  simp

theorem vonMangoldtSquareHyperbolaMass_pow_two_le_quadraticIncrementConvolution
    (M : ℕ) :
    vonMangoldtSquareHyperbolaMass (2 ^ M) ≤
      quadraticIncrementConvolution vonMangoldtSquareDyadicProfile M := by
  rw [vonMangoldtSquareHyperbolaMass_eq_dyadic_blocks]
  have hblock : ∀ k ∈ Finset.range M,
      (∑ d ∈ Finset.Ioc (2 ^ (M - (k + 1))) (2 ^ (M - k)),
          vonMangoldtSquareHarmonicWeight d *
            vonMangoldtHarmonicSquareSum (2 ^ M / d)) ≤
        (vonMangoldtSquareDyadicProfile (M - k) -
          vonMangoldtSquareDyadicProfile (M - (k + 1))) *
          vonMangoldtSquareDyadicProfile (k + 1) := by
    intro k hk
    have hkM : k < M := Finset.mem_range.mp hk
    change (∑ d ∈ Finset.Ioc (2 ^ (M - (k + 1))) (2 ^ (M - k)),
        vonMangoldtSquareHarmonicWeight d *
          vonMangoldtHarmonicSquareSum (2 ^ M / d)) ≤
      (vonMangoldtHarmonicSquareSum (2 ^ (M - k)) -
        vonMangoldtHarmonicSquareSum (2 ^ (M - (k + 1)))) *
        vonMangoldtHarmonicSquareSum (2 ^ (k + 1))
    have hlo1 : 1 ≤ 2 ^ (M - (k + 1)) := one_le_pow₀ (by norm_num)
    have hlohi : 2 ^ (M - (k + 1)) ≤ 2 ^ (M - k) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    rw [← sum_Ioc_vonMangoldtSquareHarmonicWeight_eq_sub hlo1 hlohi]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d hd
    have hdlo : 2 ^ (M - (k + 1)) < d := (Finset.mem_Ioc.mp hd).1
    have hcut := dyadic_upper_div_cutoff hkM hdlo
    exact mul_le_mul_of_nonneg_left
      (monotone_vonMangoldtHarmonicSquareSum hcut)
      (vonMangoldtSquareHarmonicWeight_nonneg d)
  refine (Finset.sum_le_sum hblock).trans_eq ?_
  rw [quadraticIncrementConvolution]
  have hreflect := Finset.sum_range_reflect
    (fun j => (vonMangoldtSquareDyadicProfile (j + 1) -
      vonMangoldtSquareDyadicProfile j) *
      vonMangoldtSquareDyadicProfile (M - j)) M
  rw [← hreflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hkM : k < M := Finset.mem_range.mp hk
  have h1 : M - 1 - k + 1 = M - k := by omega
  have h2 : M - 1 - k = M - (k + 1) := by omega
  have h3 : M - (M - (k + 1)) = k + 1 := by omega
  rw [h1, h2, h3]

end RHTower.Sieve
