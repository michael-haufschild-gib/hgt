import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The proper prime powers in `Σ Λ(n)/√n`

The non-prime terms of `Σ_{n ≤ N} Λ(n)/√n` come from proper prime powers `p^k`, `k ≥ 2`, and
contribute `O(log N)` (`sum_nonprime_vonMangoldt_div_sqrt_le`):

  `Σ_{n ≤ N, n not prime} Λ(n)/√n ≤ 2 log N + 4 log 4 + 16`.

The terms are `log p · p^{−k/2}`.  For fixed `p ≤ √N` the geometric tail over `k ≥ 2` is at most
`4/p`, and `Σ_{p ≤ √N} log p/p ≤ log √N + log 4 + 4` is Mertens' first theorem.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace RHTower

noncomputable section

theorem sqrt_natCast_pow (p k : ℕ) : Real.sqrt ((p ^ k : ℕ) : ℝ) = Real.sqrt p ^ k := by
  have h : (Real.sqrt p ^ k) ^ 2 = ((p ^ k : ℕ) : ℝ) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)]; push_cast; ring
  rw [← h, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]

/-- The geometric tail `Σ_{2 ≤ k < n} p^{−k/2} ≤ 4/p` for a prime `p`. -/
theorem sum_Ico_two_inv_sqrt_pow_le {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∑ k ∈ Ico 2 n, (1 / Real.sqrt p) ^ k ≤ 4 / p := by
  set r := 1 / Real.sqrt p with hr
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsp : (4 : ℝ) / 3 ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hr0 : 0 ≤ r := by positivity
  have hr34 : r ≤ 3 / 4 := by
    rw [hr, div_le_iff₀ (by linarith)]; nlinarith
  have hr1 : r < 1 := by linarith
  have hrsq : r ^ 2 = 1 / p := by
    rw [hr, div_pow, Real.sq_sqrt (by linarith), one_pow]
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 2) (n := n) hr0 hr1
  have h1r : 0 < 1 - r := by linarith
  have hbound : r ^ 2 / (1 - r) ≤ 4 * r ^ 2 := by
    rw [div_le_iff₀ h1r]; nlinarith
  have h4 : 4 * r ^ 2 = 4 / p := by rw [hrsq]; ring
  linarith

/-- **Proper prime powers.**  `Σ_{n ≤ N, n not prime} Λ(n)/√n ≤ 2 log N + 4 log 4 + 16`. -/
theorem sum_nonprime_vonMangoldt_div_sqrt_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N with ¬ n.Prime, Λ n / Real.sqrt n ≤
      2 * Real.log N + 4 * Real.log 4 + 16 := by
  classical
  set g : ℕ → ℝ := fun n => if n.Prime then 0 else Λ n / Real.sqrt n with hg
  -- restrict to prime powers
  have hstep1 : ∑ n ∈ Ioc 0 N with ¬ n.Prime, Λ n / Real.sqrt n =
      ∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊ with IsPrimePow n, g n := by
    rw [Nat.floor_natCast, sum_filter, sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hpp : IsPrimePow n
    · by_cases hpr : n.Prime
      · simp [hpr, hg]
      · simp [hpr, hpp, hg]
    · have hΛ : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
      simp [hpp, hΛ]
  rw [hstep1, Chebyshev.sum_PrimePow_eq_sum_sum g (Nat.cast_nonneg N)]
  set M := ⌊Real.sqrt N⌋₊ with hM
  set P := (Ioc 0 M).filter Nat.Prime with hP
  set K := ⌊Real.log N / Real.log 2⌋₊
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogp : ∀ p ∈ P, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
  -- bound for `k ≥ 2`
  have hinner : ∀ k ∈ Ico 2 (K + 1),
      ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime, g (p ^ k) ≤
        ∑ p ∈ P, Real.log p * (1 / Real.sqrt p) ^ k := by
    intro k hk
    have h2 : 2 ≤ k := (mem_Ico.mp hk).1
    have hval : ∀ p, p.Prime → g (p ^ k) = Real.log p * (1 / Real.sqrt p) ^ k := by
      intro p hp
      have hnp : ¬ (p ^ k).Prime := Nat.Prime.not_prime_pow' (by omega)
      simp only [hg, if_neg hnp, ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime hp, sqrt_natCast_pow, one_div_pow, mul_one_div]
    have hsub : (Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime ⊆ P := by
      intro p hp
      rw [mem_filter, mem_Ioc] at hp ⊢
      refine ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_le_floor ?_)⟩, hp.2⟩
      rw [Real.sqrt_eq_rpow]
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < k)) (by norm_num)]
      have : (2 : ℝ) ≤ k := by exact_mod_cast h2
      linarith
    calc ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime, g (p ^ k)
        = ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
            Real.log p * (1 / Real.sqrt p) ^ k :=
          Finset.sum_congr rfl fun p hp => hval p (mem_filter.mp hp).2
      _ ≤ ∑ p ∈ P, Real.log p * (1 / Real.sqrt p) ^ k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
            mul_nonneg (hlogp p hp) (by positivity)
  -- split off `k = 1`
  by_cases hK0 : K = 0
  · simp only [hK0, Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), sum_empty]
    have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hIcc : Icc 1 K = Ico 1 (K + 1) := rfl
  rw [hIcc, Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < K + 1)]
  have hk1 : ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (1 : ℕ))⌋₊ with p.Prime, g (p ^ 1) = 0 :=
    Finset.sum_eq_zero fun p hp => by simp [hg, (mem_filter.mp hp).2]
  rw [hk1, zero_add]
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [Finset.sum_comm]
  have htail : ∀ p ∈ P, ∑ k ∈ Ico 2 (K + 1), Real.log p * (1 / Real.sqrt p) ^ k ≤
      4 * (Real.log p / p) := by
    intro p hp
    rw [← Finset.mul_sum]
    calc Real.log p * ∑ k ∈ Ico 2 (K + 1), (1 / Real.sqrt p) ^ k
        ≤ Real.log p * (4 / p) :=
          mul_le_mul_of_nonneg_left (sum_Ico_two_inv_sqrt_pow_le (mem_filter.mp hp).2 _)
            (hlogp p hp)
      _ = 4 * (Real.log p / p) := by ring
  refine (Finset.sum_le_sum htail).trans ?_
  rw [← Finset.mul_sum]
  -- Mertens over the primes up to `√N`
  have hM1 : 1 ≤ M := by
    rw [hM, Nat.le_floor_iff (Real.sqrt_nonneg _)]
    push_cast
    exact Real.one_le_sqrt.mpr hN1
  have hmert := Mertens.mertens_first M hM1
  have hsubP : ∑ p ∈ P, Real.log p / p ≤ ∑ d ∈ Icc 1 M, Λ d / d := by
    have hsub : P ⊆ Icc 1 M := by
      intro p hp
      rw [mem_filter, mem_Ioc] at hp
      exact mem_Icc.mpr ⟨hp.1.1, hp.1.2⟩
    calc ∑ p ∈ P, Real.log p / p = ∑ p ∈ P, Λ p / p :=
          Finset.sum_congr rfl fun p hp => by
            rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
      _ ≤ ∑ d ∈ Icc 1 M, Λ d / d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ =>
            div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
  have hlogM : Real.log M ≤ Real.log N / 2 := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have h1 : (M : ℝ) ≤ Real.sqrt N := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 := Real.log_le_log hM0 h1
    rw [Real.log_sqrt (Nat.cast_nonneg N)] at h2
    exact h2
  rw [abs_le] at hmert
  linarith [hmert.2]

end

end RHTower
