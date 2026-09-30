import GaloisForLFunctions.RHTower.MertensThirdTheorem

/-!
# Gronwall's theorem and Robin's inequality on `k`-free integers

Robin's criterion reads RH ⇔ `σ(n) < e^γ n log log n` for all `n > 5040`. This module proves the
unconditional parts that follow from Mertens' third theorem `∏_{p ≤ N}(1 − 1/p) log N → e^{−γ}`
(`tendsto_mertensPrimeProduct_mul_log`).

* `σ(n)/n = ∏_{p ∣ n} (1 − p^{−(a_p+1)})/(1 − 1/p)` (`sigma_div_eq_prod`).
* For every `N ≥ 2`, with `S_{>N}` the prime factors of `n` above `N`,
  `σ(n)/n ≤ (∏_{p ≤ N}(1 − 1/p))^{−1} (1 + 1/N)^{|S_{>N}|}`, and `(N+1)^{|S_{>N}|} ≤ n`
  (`sigma_div_le_mertens_mul_tail`, `pow_card_primeFactors_gt_le`). If `n` is `k`-free, the
  factor `1 − 2^{−k}` can be inserted (`sigma_div_le_mertens_mul_tail_kFree`): for even `n` it comes
  from `σ(2^a)/2^a = 2 − 2^{−a}`, `a < k`, and for odd `n` the missing factor `2` of the Mertens product
  gives `1/2 ≤ 1 − 2^{−k}`.
* **Gronwall (upper half).** For every `ε > 0`, eventually `σ(n) ≤ (e^γ + ε) n log log n`
  (`eventually_sigma_le_gronwall`).
* **Robin away from high powers of two.** For every `k ≥ 1`, eventually every `n` with `2^k ∤ n`
  (in particular every `k`-free `n`) satisfies `σ(n) < e^γ n log log n`
  (`eventually_sigma_lt_robin_of_not_two_pow_dvd`). Counterexamples to Robin's inequality, if any,
  therefore have `v₂(n) → ∞`.
* **The defect criterion.** For every `δ > 0`, eventually every `n` with
  `Σ_{p ≤ log n} p^{−(v_p(n)+1)} ≥ δ` satisfies Robin's inequality
  (`eventually_sigma_lt_robin_of_defect`), since `σ(n)/n ≤ (∏_{p≤N}(1−1/p))^{−1}
  e^{−Σ_{p≤N} p^{−(v_p(n)+1)}} (1 + 1/N)^{|S_{>N}|}` (`sigma_div_le_mertens_defect`). A missing prime
  `p ≤ log n` contributes `1/p`. So counterexamples, if any, have defect `→ 0`: every fixed prime
  divides them to an unbounded power, and they miss only primes of negligible harmonic mass.
* **Gronwall (lower half).** For every `ε > 0`, `σ(n) ≥ (e^γ − ε) n log log n` for arbitrarily
  large `n` (`frequently_sigma_ge_gronwall`), at the primorial powers `n = ∏_{p ≤ y} p^m`,
  `m = ⌈log y⌉ + 1`, where `σ(n)/n ≥ (∏_{p ≤ y}(1 − 1/p))^{−1}(1 − 2^{1−m})` and
  `log n = m θ(y) ≤ 6my`. So `limsup σ(n)/(n log log n) = e^γ`: Robin's inequality has no slack.
-/

open ArithmeticFunction Filter Finset

namespace RHTower

noncomputable section

/-! ## The local factors -/

/-- `σ(p^a)/p^a = (1 − p^{−(a+1)})/(1 − 1/p)`. -/
theorem sigma_prime_pow_div {p a : ℕ} (hp : p.Prime) :
    ((sigma 1 (p ^ a) : ℕ) : ℝ) / (p : ℝ) ^ a = (1 - (1 / (p : ℝ)) ^ (a + 1)) / (1 - 1 / p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_eq (by linarith : (p : ℝ) ≠ 1)]
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : 1 - 1 / (p : ℝ) ≠ 0 := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; exact hp1
    linarith
  rw [one_div_pow]
  field_simp
  ring

/-- **The product formula** `σ(n)/n = ∏_{p ∣ n} (1 − p^{−(a_p+1)})/(1 − 1/p)`. -/
theorem sigma_div_eq_prod {n : ℕ} (hn : n ≠ 0) :
    ((sigma 1 n : ℕ) : ℝ) / n =
      ∏ p ∈ n.primeFactors, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p) := by
  have hσ := (isMultiplicative_sigma (k := 1)).multiplicative_factorization (sigma 1) hn
  have hn' := Nat.prod_factorization_pow_eq_self hn
  unfold Finsupp.prod at hσ hn'
  rw [Nat.support_factorization] at hσ hn'
  have hσR : ((sigma 1 n : ℕ) : ℝ) = ∏ p ∈ n.primeFactors, ((sigma 1 (p ^ n.factorization p) : ℕ) : ℝ) := by
    rw [hσ]; push_cast; rfl
  have hnR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    conv_lhs => rw [← hn']
    push_cast; rfl
  rw [hσR, hnR, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact sigma_prime_pow_div (Nat.prime_of_mem_primeFactors hp)

theorem one_le_inv_one_sub_inv {p : ℕ} (hp : p.Prime) : 1 ≤ (1 - 1 / (p : ℝ))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  rw [one_le_inv₀ h1]
  have : 0 ≤ 1 / (p : ℝ) := by positivity
  linarith

/-- A local factor is at most `(1 − 1/p)^{−1}`. -/
theorem local_factor_le {p a : ℕ} (hp : p.Prime) :
    (1 - (1 / (p : ℝ)) ^ (a + 1)) / (1 - 1 / p) ≤ (1 - 1 / (p : ℝ))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  rw [div_eq_mul_inv]
  have h2 : 0 ≤ (1 / (p : ℝ)) ^ (a + 1) := by positivity
  have h3 : 0 < (1 - 1 / (p : ℝ))⁻¹ := inv_pos.mpr h1
  nlinarith

theorem local_factor_nonneg {p a : ℕ} (hp : p.Prime) :
    0 ≤ (1 - (1 / (p : ℝ)) ^ (a + 1)) / (1 - 1 / p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  have h2 : (1 / (p : ℝ)) ^ (a + 1) ≤ 1 := pow_le_one₀ (by positivity) (by
    rw [div_le_one (by linarith)]; linarith)
  exact div_nonneg (by linarith) h1.le

/-- At `p = 2` with `a < k`: `σ(2^a)/2^a ≤ 2(1 − 2^{−k})`. -/
theorem local_factor_two_le {a k : ℕ} (hak : a < k) :
    (1 - (1 / (2 : ℝ)) ^ (a + 1)) / (1 - 1 / 2) ≤ (1 - (1 / 2 : ℝ) ^ k) * (1 - 1 / (2 : ℝ))⁻¹ := by
  have h : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ (a + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [div_eq_mul_inv]
  have h3 : 0 < (1 - 1 / (2 : ℝ))⁻¹ := by norm_num
  nlinarith

/-! ## Comparison with the Mertens product -/

/-- The inverse Mertens product is the product of `(1 − 1/p)^{−1}` over the primes `≤ N`. -/
theorem inv_mertensPrimeProduct_eq (N : ℕ) :
    (mertensPrimeProduct N)⁻¹ =
      ∏ p ∈ (Finset.Icc 0 N).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹ := by
  unfold mertensPrimeProduct
  rw [← Finset.prod_inv_distrib, Finset.prod_filter]
  refine Finset.prod_congr rfl fun n _ => ?_
  split_ifs <;> simp [one_div]

/-- A set of primes `≤ N` contributes at most the inverse Mertens product. -/
theorem prod_inv_le_inv_mertens {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {N : ℕ}
    (hSN : ∀ p ∈ S, p ≤ N) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ (mertensPrimeProduct N)⁻¹ := by
  rw [inv_mertensPrimeProduct_eq]
  refine Finset.prod_le_prod_of_subset_of_one_le (fun p hp => ?_)
    (fun p hp => le_trans zero_le_one (one_le_inv_one_sub_inv (hS p hp))) (fun p hp _ => ?_)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hSN p hp⟩, hS p hp⟩
  · exact one_le_inv_one_sub_inv (Finset.mem_filter.mp hp).2

/-- An odd set of primes `≤ N` contributes at most half the inverse Mertens product. -/
theorem prod_inv_le_half_inv_mertens {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {N : ℕ}
    (hN : 2 ≤ N) (hSN : ∀ p ∈ S, p ≤ N) (h2 : 2 ∉ S) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ 1 / 2 * (mertensPrimeProduct N)⁻¹ := by
  have hS2 : ∏ p ∈ insert 2 S, (1 - 1 / (p : ℝ))⁻¹ ≤ (mertensPrimeProduct N)⁻¹ :=
    prod_inv_le_inv_mertens (fun p hp => by
      rcases Finset.mem_insert.mp hp with h | h
      · rw [h]; exact Nat.prime_two
      · exact hS p h) (fun p hp => by
      rcases Finset.mem_insert.mp hp with h | h
      · rw [h]; exact hN
      · exact hSN p h)
  rw [Finset.prod_insert h2, show (1 - 1 / ((2 : ℕ) : ℝ))⁻¹ = 2 by norm_num] at hS2
  linarith

/-! ## The upper bound -/

/-- The primes of `n` above `N` number at most `log n / log(N+1)`: `(N+1)^{|S_{>N}|} ≤ n`. -/
theorem pow_card_primeFactors_gt_le {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    (N + 1) ^ (n.primeFactors.filter (N < ·)).card ≤ n := by
  calc (N + 1) ^ (n.primeFactors.filter (N < ·)).card
      ≤ ∏ p ∈ n.primeFactors.filter (N < ·), p :=
        Finset.pow_card_le_prod _ _ _ fun p hp => (Finset.mem_filter.mp hp).2
    _ ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
          fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- The large primes of `n` contribute at most `(1 + 1/N)` each. -/
theorem prod_inv_gt_le {n N : ℕ} (hN : 1 ≤ N) :
    ∏ p ∈ n.primeFactors.filter (N < ·), (1 - 1 / (p : ℝ))⁻¹ ≤
      (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card := by
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun p hp => le_trans zero_le_one
    (one_le_inv_one_sub_inv (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)))
    fun p hp => ?_
  obtain ⟨hpS, hNp⟩ := Finset.mem_filter.mp hp
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpr : (N : ℝ) + 1 ≤ p := by exact_mod_cast hNp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : 1 - 1 / (p : ℝ) = (p - 1) / p := by field_simp
  rw [h1, inv_div, div_le_iff₀ (by linarith)]
  have e : (1 + 1 / (N : ℝ)) * (p - 1) = p - 1 + (p - 1) / N := by field_simp
  rw [e]
  have : 1 ≤ ((p : ℝ) - 1) / N := by rw [le_div_iff₀ (by linarith)]; linarith
  linarith

/-- **The Mertens bound for `σ(n)/n`.** -/
theorem sigma_div_le_mertens_mul_tail {n N : ℕ} (hn : n ≠ 0) (hN : 1 ≤ N) :
    ((sigma 1 n : ℕ) : ℝ) / n ≤ (mertensPrimeProduct N)⁻¹ *
      (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card := by
  rw [sigma_div_eq_prod hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (· ≤ N)]
  have hpr : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfilt : n.primeFactors.filter (fun p => ¬ p ≤ N) = n.primeFactors.filter (N < ·) := by
    ext p; simp [not_le]
  rw [hfilt]
  have h1 : ∏ p ∈ n.primeFactors.filter (· ≤ N),
      (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p) ≤ (mertensPrimeProduct N)⁻¹ :=
    (Finset.prod_le_prod (fun p hp => local_factor_nonneg (hpr p (Finset.mem_filter.mp hp).1))
      (fun p hp => local_factor_le (hpr p (Finset.mem_filter.mp hp).1))).trans
      (prod_inv_le_inv_mertens (fun p hp => hpr p (Finset.mem_filter.mp hp).1)
        (fun p hp => (Finset.mem_filter.mp hp).2))
  have h2 : ∏ p ∈ n.primeFactors.filter (N < ·),
      (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p) ≤
        (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card :=
    (Finset.prod_le_prod (fun p hp => local_factor_nonneg (hpr p (Finset.mem_filter.mp hp).1))
      (fun p hp => local_factor_le (hpr p (Finset.mem_filter.mp hp).1))).trans (prod_inv_gt_le hN)
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun p hp =>
    local_factor_nonneg (hpr p (Finset.mem_filter.mp hp).1)) (inv_nonneg.mpr
      (mertensPrimeProduct_pos N).le)

/-- **The Mertens bound for `k`-free `n`**, with the extra factor `1 − 2^{−k}`. -/
theorem sigma_div_le_mertens_mul_tail_kFree {n N k : ℕ} (hn : n ≠ 0) (hN : 2 ≤ N) (hk : 1 ≤ k)
    (hfree : ¬ 2 ^ k ∣ n) :
    ((sigma 1 n : ℕ) : ℝ) / n ≤ (1 - (1 / 2 : ℝ) ^ k) * (mertensPrimeProduct N)⁻¹ *
      (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card := by
  rw [sigma_div_eq_prod hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (· ≤ N)]
  have hpr : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfilt : n.primeFactors.filter (fun p => ¬ p ≤ N) = n.primeFactors.filter (N < ·) := by
    ext p; simp [not_le]
  rw [hfilt]
  set S := n.primeFactors.filter (· ≤ N) with hS
  have hSpr : ∀ p ∈ S, p.Prime := fun p hp => hpr p (Finset.mem_filter.mp hp).1
  have hSN : ∀ p ∈ S, p ≤ N := fun p hp => (Finset.mem_filter.mp hp).2
  have hc : (1 / 2 : ℝ) ≤ 1 - (1 / 2) ^ k := by
    have : (1 / 2 : ℝ) ^ k ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hM0 : 0 ≤ (mertensPrimeProduct N)⁻¹ := inv_nonneg.mpr (mertensPrimeProduct_pos N).le
  have h1 : ∏ p ∈ S, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p) ≤
      (1 - (1 / 2 : ℝ) ^ k) * (mertensPrimeProduct N)⁻¹ := by
    by_cases h2 : 2 ∈ S
    · rw [← Finset.mul_prod_erase S _ h2]
      have ha : n.factorization 2 < k := by
        by_contra h
        push Not at h
        exact hfree ((Nat.prime_two.pow_dvd_iff_le_factorization hn).mpr h)
      have hf2 := local_factor_two_le ha
      have hrest : ∏ p ∈ S.erase 2, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p) ≤
          ∏ p ∈ S.erase 2, (1 - 1 / (p : ℝ))⁻¹ :=
        Finset.prod_le_prod (fun p hp => local_factor_nonneg (hSpr p (Finset.mem_of_mem_erase hp)))
          (fun p hp => local_factor_le (hSpr p (Finset.mem_of_mem_erase hp)))
      have hall : (1 - 1 / (2 : ℝ))⁻¹ * ∏ p ∈ S.erase 2, (1 - 1 / (p : ℝ))⁻¹ ≤
          (mertensPrimeProduct N)⁻¹ := by
        have e := Finset.mul_prod_erase S (fun p : ℕ => (1 - 1 / (p : ℝ))⁻¹) h2
        simp only [Nat.cast_ofNat] at e
        rw [e]
        exact prod_inv_le_inv_mertens hSpr hSN
      have hr0 : 0 ≤ ∏ p ∈ S.erase 2, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p) :=
        Finset.prod_nonneg fun p hp => local_factor_nonneg (hSpr p (Finset.mem_of_mem_erase hp))
      have hck : 0 ≤ 1 - (1 / 2 : ℝ) ^ k := by linarith
      calc (1 - (1 / (2 : ℝ)) ^ (n.factorization 2 + 1)) / (1 - 1 / 2) *
            ∏ p ∈ S.erase 2, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p)
          ≤ (1 - (1 / 2 : ℝ) ^ k) * (1 - 1 / (2 : ℝ))⁻¹ *
              ∏ p ∈ S.erase 2, (1 - 1 / (p : ℝ))⁻¹ :=
            mul_le_mul hf2 hrest hr0 (by positivity)
        _ = (1 - (1 / 2 : ℝ) ^ k) * ((1 - 1 / (2 : ℝ))⁻¹ *
              ∏ p ∈ S.erase 2, (1 - 1 / (p : ℝ))⁻¹) := by ring
        _ ≤ (1 - (1 / 2 : ℝ) ^ k) * (mertensPrimeProduct N)⁻¹ :=
            mul_le_mul_of_nonneg_left hall hck
    · have hodd := prod_inv_le_half_inv_mertens hSpr hN hSN h2
      calc ∏ p ∈ S, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p)
          ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ :=
            Finset.prod_le_prod (fun p hp => local_factor_nonneg (hSpr p hp))
              (fun p hp => local_factor_le (hSpr p hp))
        _ ≤ 1 / 2 * (mertensPrimeProduct N)⁻¹ := hodd
        _ ≤ (1 - (1 / 2 : ℝ) ^ k) * (mertensPrimeProduct N)⁻¹ :=
            mul_le_mul_of_nonneg_right hc hM0
  have h2 : ∏ p ∈ n.primeFactors.filter (N < ·),
      (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p) ≤
        (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card :=
    (Finset.prod_le_prod (fun p hp => local_factor_nonneg (hpr p (Finset.mem_filter.mp hp).1))
      (fun p hp => local_factor_le (hpr p (Finset.mem_filter.mp hp).1))).trans
        (prod_inv_gt_le (by omega))
  have hc0 : 0 ≤ (1 - (1 / 2 : ℝ) ^ k) * (mertensPrimeProduct N)⁻¹ := by
    have : 0 ≤ 1 - (1 / 2 : ℝ) ^ k := by linarith
    positivity
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun p hp =>
    local_factor_nonneg (hpr p (Finset.mem_filter.mp hp).1)) hc0

/-! ## Asymptotics -/

/-- The large primes cost at most `e^{2/log log n}`: with `N = ⌊log n⌋` and `(N+1)^c ≤ n`,
`(1 + 1/N)^c ≤ e^{2/log log n}`. -/
theorem one_add_inv_pow_le_exp {n N c : ℕ} (hn : 16 ≤ n) (hNdef : N = ⌊Real.log n⌋₊)
    (hc : (N + 1) ^ c ≤ n) :
    (1 + 1 / (N : ℝ)) ^ c ≤ Real.exp (2 / Real.log (Real.log n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : 2 ≤ Real.log n := by
    have h16 : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hN1 : Real.log n - 1 < N := by
    rw [hNdef]; have := Nat.lt_floor_add_one (Real.log n); linarith
  have hNle : (N : ℝ) ≤ Real.log n := by rw [hNdef]; exact Nat.floor_le (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  have hloglog : 0 < Real.log (Real.log n) := Real.log_pos (by linarith)
  have hN1r : Real.log n < (N : ℝ) + 1 := by linarith
  have hcl : (c : ℝ) * Real.log ((N : ℝ) + 1) ≤ Real.log n := by
    have h := Real.log_le_log (by positivity) (show (((N + 1) ^ c : ℕ) : ℝ) ≤ n by exact_mod_cast hc)
    push_cast at h
    rwa [Real.log_pow] at h
  have hlogN1 : Real.log (Real.log n) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by linarith) hN1r.le
  have hc' : (c : ℝ) ≤ Real.log n / Real.log (Real.log n) := by
    rw [le_div_iff₀ hloglog]
    have := mul_le_mul_of_nonneg_left hlogN1 (Nat.cast_nonneg c)
    linarith
  calc (1 + 1 / (N : ℝ)) ^ c ≤ Real.exp (1 / N) ^ c := by
        refine pow_le_pow_left₀ (by positivity) ?_ c
        have := Real.add_one_le_exp (1 / (N : ℝ)); linarith
    _ = Real.exp (c * (1 / N)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2 / Real.log (Real.log n)) := by
        apply Real.exp_le_exp.mpr
        have hN2 : Real.log n / 2 ≤ N := by linarith
        calc (c : ℝ) * (1 / N) ≤ Real.log n / Real.log (Real.log n) * (1 / N) :=
              mul_le_mul_of_nonneg_right hc' (by positivity)
          _ ≤ Real.log n / Real.log (Real.log n) * (2 / Real.log n) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [div_le_div_iff₀ hNpos (by linarith)]
              linarith
          _ = 2 / Real.log (Real.log n) := by field_simp

/-- Mertens' third theorem in the form `(∏_{p ≤ N}(1 − 1/p))^{−1} ≤ (1+η) e^γ log N`, eventually. -/
theorem eventually_inv_mertens_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (mertensPrimeProduct N)⁻¹ ≤
      (1 + η) * Real.exp Real.eulerMascheroniConstant * Real.log N := by
  have h := tendsto_mertensPrimeProduct_mul_log
  have hlt : Real.exp (-Real.eulerMascheroniConstant) / (1 + η) <
      Real.exp (-Real.eulerMascheroniConstant) := by
    rw [div_lt_iff₀ (by linarith)]
    have := Real.exp_pos (-Real.eulerMascheroniConstant)
    nlinarith
  filter_upwards [(tendsto_order.1 h).1 _ hlt, eventually_ge_atTop 2] with N hN hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hM := mertensPrimeProduct_pos N
  rw [inv_le_iff_one_le_mul₀ hM]
  have hE : Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add]; simp
  have h1 := mul_lt_mul_of_pos_left hN (show 0 < (1 + η) * Real.exp Real.eulerMascheroniConstant
    by positivity)
  have e : (1 + η) * Real.exp Real.eulerMascheroniConstant *
      (Real.exp (-Real.eulerMascheroniConstant) / (1 + η)) = 1 := by
    field_simp
    linarith [hE, mul_comm (Real.exp Real.eulerMascheroniConstant)
      (Real.exp (-Real.eulerMascheroniConstant))]
  rw [e] at h1
  nlinarith

/-- The floor of `log n` tends to infinity. -/
theorem tendsto_floor_log_nat : Tendsto (fun n : ℕ => ⌊Real.log n⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `log log n → ∞`. -/
theorem tendsto_log_log_nat : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The common bound `σ(n)/n ≤ c (1+η)² e^γ log log n` behind both theorems. -/
theorem eventually_sigma_div_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, 16 ≤ n ∧ 0 < Real.log (Real.log n) ∧
      (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ *
          (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card ≤
        (1 + η) ^ 2 * Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by
  have hM := tendsto_floor_log_nat.eventually (eventually_inv_mertens_le hη)
  have hL := tendsto_log_log_nat.eventually (eventually_ge_atTop (2 / Real.log (1 + η)))
  have hlogη : 0 < Real.log (1 + η) := Real.log_pos (by linarith)
  filter_upwards [hM, hL, eventually_ge_atTop 16] with n hMn hLn hn16
  have hn0 : n ≠ 0 := by omega
  set N := ⌊Real.log n⌋₊ with hN
  have hlog2 : 2 ≤ Real.log n := by
    have h16 : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn16)
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hll : 0 < Real.log (Real.log n) := Real.log_pos (by linarith)
  refine ⟨hn16, hll, ?_⟩
  have htail := one_add_inv_pow_le_exp hn16 hN (pow_card_primeFactors_gt_le hn0 N)
  have hexp : Real.exp (2 / Real.log (Real.log n)) ≤ 1 + η := by
    rw [← Real.exp_log (show (0 : ℝ) < 1 + η by linarith)]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hll]
    have := (div_le_iff₀ hlogη).mp hLn
    linarith
  have hNle : (N : ℝ) ≤ Real.log n := Nat.floor_le (by linarith)
  have hN2 : 2 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hlogN : Real.log N ≤ Real.log (Real.log n) :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hNle
  have hMn' : (mertensPrimeProduct N)⁻¹ ≤
      (1 + η) * Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) :=
    hMn.trans (mul_le_mul_of_nonneg_left hlogN (by positivity))
  calc (mertensPrimeProduct N)⁻¹ * (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card
      ≤ ((1 + η) * Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) * (1 + η) :=
        mul_le_mul hMn' (htail.trans hexp) (by positivity) (by positivity)
    _ = (1 + η) ^ 2 * Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by ring

theorem two_le_floor_log {n : ℕ} (hn : 16 ≤ n) : 2 ≤ ⌊Real.log n⌋₊ := by
  have hlog2 : 2 ≤ Real.log n := by
    have h16 : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  exact Nat.le_floor (by push_cast; linarith)

/-- **Gronwall's theorem, upper half.** For every `ε > 0`, eventually
`σ(n) ≤ (e^γ + ε) n log log n`. -/
theorem eventually_sigma_le_gronwall {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((sigma 1 n : ℕ) : ℝ) ≤
      (Real.exp Real.eulerMascheroniConstant + ε) * n * Real.log (Real.log n) := by
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  set η := min 1 (ε / (4 * E)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / (4 * E) := min_le_right _ _
  filter_upwards [eventually_sigma_div_le hη0] with n ⟨hn16, hll, hbound⟩
  have hn0 : n ≠ 0 := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN := two_le_floor_log hn16
  have hσ := (sigma_div_le_mertens_mul_tail hn0 (by omega : 1 ≤ ⌊Real.log n⌋₊)).trans hbound
  rw [div_le_iff₀ hnr] at hσ
  have hc : (1 + η) ^ 2 * E ≤ E + ε := by
    have h1 : (1 + η) ^ 2 ≤ 1 + 3 * η := by nlinarith
    have h2 : E * (3 * η) ≤ 3 * ε / 4 := by
      have := mul_le_mul_of_nonneg_left hηε hE0.le
      rw [show E * (ε / (4 * E)) = ε / 4 by field_simp] at this
      linarith
    nlinarith
  calc ((sigma 1 n : ℕ) : ℝ) ≤ (1 + η) ^ 2 * E * Real.log (Real.log n) * n := hσ
    _ ≤ (E + ε) * Real.log (Real.log n) * n := by gcongr
    _ = (E + ε) * n * Real.log (Real.log n) := by ring

/-- **Robin's inequality away from high powers of two.** For every `k ≥ 1`, eventually every `n`
with `2^k ∤ n` satisfies `σ(n) < e^γ n log log n`. In particular Robin's inequality holds
eventually on every class of `k`-free integers. -/
theorem eventually_sigma_lt_robin_of_not_two_pow_dvd {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ¬ 2 ^ k ∣ n → ((sigma 1 n : ℕ) : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  set x : ℝ := (1 / 2) ^ k with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  filter_upwards [eventually_sigma_div_le (η := x / 4) (by positivity)] with n ⟨hn16, hll, hbound⟩
    hfree
  have hn0 : n ≠ 0 := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN := two_le_floor_log hn16
  have hσ := sigma_div_le_mertens_mul_tail_kFree hn0 hN hk hfree
  have hc : (1 - x) * ((1 + x / 4) ^ 2 * E) < E := by
    have e : (1 - x) * (1 + x / 4) ^ 2 = 1 - x / 2 - 7 * x ^ 2 / 16 - x ^ 3 / 16 := by ring
    have h1 : (1 - x) * (1 + x / 4) ^ 2 < 1 := by
      rw [e]; have : 0 < x ^ 2 := by positivity
      have : 0 < x ^ 3 := by positivity
      linarith
    have := mul_lt_mul_of_pos_right h1 hE0
    linarith
  have h1x : 0 ≤ 1 - x := by linarith
  have hσ' : ((sigma 1 n : ℕ) : ℝ) / n ≤
      (1 - x) * ((1 + x / 4) ^ 2 * E * Real.log (Real.log n)) := by
    refine hσ.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hbound h1x
  rw [div_le_iff₀ hnr] at hσ'
  calc ((sigma 1 n : ℕ) : ℝ) ≤ (1 - x) * ((1 + x / 4) ^ 2 * E * Real.log (Real.log n)) * n := hσ'
    _ = ((1 - x) * ((1 + x / 4) ^ 2 * E)) * Real.log (Real.log n) * n := by ring
    _ < E * Real.log (Real.log n) * n := by
        apply mul_lt_mul_of_pos_right _ hnr
        exact mul_lt_mul_of_pos_right hc hll
    _ = E * n * Real.log (Real.log n) := by ring

/-! ## Sharpness: the primorial powers -/

/-- `∏(1 − a_i) ≥ 1 − Σ a_i` for `0 ≤ a_i ≤ 1`. -/
theorem prod_one_sub_ge_one_sub_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => ha0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
    have hj0 := ha0 j (Finset.mem_insert_self j s)
    have hj1 := ha1 j (Finset.mem_insert_self j s)
    have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    have := mul_le_mul_of_nonneg_left ih' (by linarith : 0 ≤ 1 - a j)
    nlinarith

/-- The primorial power `∏_{p ≤ y} p^m`. -/
def primorialPow (y m : ℕ) : ℕ := ∏ p ∈ (Finset.Icc 0 y).filter Nat.Prime, p ^ m

theorem primorialPow_pos (y m : ℕ) : 0 < primorialPow y m :=
  Finset.prod_pos fun _ hp => pow_pos (Finset.mem_filter.mp hp).2.pos m

theorem sigma_div_primorialPow (y m : ℕ) :
    ((sigma 1 (primorialPow y m) : ℕ) : ℝ) / primorialPow y m =
      ∏ p ∈ (Finset.Icc 0 y).filter Nat.Prime, (1 - (1 / (p : ℝ)) ^ (m + 1)) / (1 - 1 / p) := by
  have hcop : ((((Finset.Icc 0 y).filter Nat.Prime : Finset ℕ)) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun p => p ^ m) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow m m ((Nat.coprime_primes (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2).mpr hpq)
  have hσ := (isMultiplicative_sigma (k := 1)).map_prod (fun p => p ^ m) _ hcop
  unfold primorialPow
  rw [hσ]
  push_cast
  rw [← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun p hp => sigma_prime_pow_div (Finset.mem_filter.mp hp).2

/-- `σ(n)/n ≥ (∏_{p ≤ y}(1 − 1/p))^{−1}(1 − 2^{1−m})` at `n = ∏_{p ≤ y} p^m`, `m ≥ 1`. -/
theorem sigma_div_primorialPow_ge (y m : ℕ) (hm : 1 ≤ m) :
    (mertensPrimeProduct y)⁻¹ * (1 - (1 / 2 : ℝ) ^ (m - 1)) ≤
      ((sigma 1 (primorialPow y m) : ℕ) : ℝ) / primorialPow y m := by
  rw [sigma_div_primorialPow, inv_mertensPrimeProduct_eq]
  set P := (Finset.Icc 0 y).filter Nat.Prime with hP
  have hpr : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have e : ∏ p ∈ P, (1 - (1 / (p : ℝ)) ^ (m + 1)) / (1 - 1 / p) =
      (∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹) * ∏ p ∈ P, (1 - (1 / (p : ℝ)) ^ (m + 1)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [div_eq_mul_inv, mul_comm]
  rw [e]
  have hsum : ∑ p ∈ P, (1 / (p : ℝ)) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ (m - 1) := by
    have h1 : ∀ p ∈ P, (1 / (p : ℝ)) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ (m - 1) * ((p : ℝ) ^ 2)⁻¹ := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hpr p hp).two_le
      have e2 : (1 / (p : ℝ)) ^ (m + 1) = (1 / (p : ℝ)) ^ (m - 1) * ((p : ℝ) ^ 2)⁻¹ := by
        rw [show m + 1 = (m - 1) + 2 by omega, pow_add, one_div_pow (n := 2), one_div, one_div]
      rw [e2]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by gcongr) _
    have h2 : ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
      have hsub : P ⊆ Finset.Ioo 1 (y + 1) := by
        intro p hp
        have := (hpr p hp).two_le
        have hpy := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
      have := sum_Ioo_inv_sq_le (α := ℝ) 1 (y + 1)
      norm_num at this
      linarith
    calc ∑ p ∈ P, (1 / (p : ℝ)) ^ (m + 1) ≤ ∑ p ∈ P, (1 / 2 : ℝ) ^ (m - 1) * ((p : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum h1
      _ = (1 / 2 : ℝ) ^ (m - 1) * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ (m - 1) * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 / 2 : ℝ) ^ (m - 1) := mul_one _
  have hprod := prod_one_sub_ge_one_sub_sum P (fun p => (1 / (p : ℝ)) ^ (m + 1))
    (fun p _ => by positivity) (fun p hp => pow_le_one₀ (by positivity) (by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hpr p hp).two_le
      rw [div_le_one (by linarith)]; linarith))
  have hM0 : 0 ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ := Finset.prod_nonneg fun p hp =>
    le_trans zero_le_one (one_le_inv_one_sub_inv (hpr p hp))
  exact mul_le_mul_of_nonneg_left (by linarith) hM0

/-- `log ∏_{p ≤ y} p^m = m θ(y) ≤ 6 m y`. -/
theorem log_primorialPow_le (y m : ℕ) :
    Real.log (primorialPow y m) ≤ 6 * m * y := by
  unfold primorialPow
  push_cast
  rw [Real.log_prod (fun p hp => by
    have := (Finset.mem_filter.mp hp).2.pos; positivity)]
  simp_rw [Real.log_pow]
  rw [← Finset.mul_sum]
  have hθ : ∑ p ∈ (Finset.Icc 0 y).filter Nat.Prime, Real.log p = Chebyshev.theta y := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  rw [hθ]
  have h1 := Chebyshev.theta_le_psi (y : ℝ)
  have h2 := Chebyshev.psi_le_const_mul_self (x := (y : ℝ)) (Nat.cast_nonneg y)
  have h4 : Real.log 4 ≤ 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num; linarith
  have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h5 : Chebyshev.theta y ≤ 6 * y := by nlinarith
  have := mul_le_mul_of_nonneg_left h5 hm
  linarith

/-- `log u ≤ 2√u` for `u > 0`. -/
theorem log_le_two_sqrt_of_pos {u : ℝ} (hu : 0 < u) : Real.log u ≤ 2 * Real.sqrt u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have h := Real.log_le_sub_one_of_pos hs
  have e : Real.log (Real.sqrt u) = Real.log u / 2 := Real.log_sqrt hu.le
  linarith

/-- `log 6 + log(log y + 2) ≤ η log y` for all large `y`. -/
theorem eventually_log_six_add_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ y : ℕ in atTop, Real.log 6 + Real.log (Real.log y + 2) ≤ η * Real.log y := by
  have hL := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (max (4 / η) (max (32 / η ^ 2) 4)))
  filter_upwards [hL] with y hy
  simp only [Function.comp] at hy
  set L := Real.log y with hLdef
  have hL4 : 4 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hL1 : 4 / η ≤ L := le_trans (le_max_left _ _) hy
  have hL2 : 32 / η ^ 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have h6 : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have := Real.exp_one_gt_d9
    nlinarith
  have hsq : Real.log (L + 2) ≤ 2 * Real.sqrt (L + 2) := log_le_two_sqrt_of_pos (by linarith)
  have hsqrt : Real.sqrt (L + 2) ≤ Real.sqrt (2 * L) := Real.sqrt_le_sqrt (by linarith)
  have hsq2 : 2 * Real.sqrt (2 * L) ≤ η * L / 2 := by
    have h0 : 0 ≤ 2 * Real.sqrt (2 * L) := by positivity
    have hsq' : (2 * Real.sqrt (2 * L)) ^ 2 ≤ (η * L / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < η ^ 2)).mp hL2
      nlinarith
    exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq'
  have h2 : 2 ≤ η * L / 2 := by
    have := (div_le_iff₀ hη).mp hL1; linarith
  linarith

/-- **Gronwall's theorem, lower half.** For every `ε > 0` there are arbitrarily large `n` with
`σ(n) ≥ (e^γ − ε) n log log n`; with the upper half, `limsup σ(n)/(n log log n) = e^γ`. -/
theorem frequently_sigma_ge_gronwall {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, (Real.exp Real.eulerMascheroniConstant - ε) * n *
      Real.log (Real.log n) ≤ ((sigma 1 n : ℕ) : ℝ) := by
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  set η := min (1 / 2) (ε / (4 * E)) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hηε : η ≤ ε / (4 * E) := min_le_right _ _
  -- Mertens from above
  have hMert : ∀ᶠ y : ℕ in atTop, (1 - η) * E * Real.log y ≤ (mertensPrimeProduct y)⁻¹ := by
    have h := tendsto_mertensPrimeProduct_mul_log
    have hlt : Real.exp (-Real.eulerMascheroniConstant) <
        Real.exp (-Real.eulerMascheroniConstant) * (1 + η) := by
      have := Real.exp_pos (-Real.eulerMascheroniConstant); nlinarith
    filter_upwards [(tendsto_order.1 h).2 _ hlt, eventually_ge_atTop 2] with y hy hy2
    have hlog : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hM := mertensPrimeProduct_pos y
    have hEinv : Real.exp (-Real.eulerMascheroniConstant) = E⁻¹ := by rw [hE, Real.exp_neg]
    rw [hEinv] at hy
    have h1 : mertensPrimeProduct y ≤ E⁻¹ * (1 + η) / Real.log y := by
      rw [le_div_iff₀ hlog]; linarith
    have h2 : (E⁻¹ * (1 + η) / Real.log y)⁻¹ ≤ (mertensPrimeProduct y)⁻¹ := inv_anti₀ hM h1
    have h3 : (E⁻¹ * (1 + η) / Real.log y)⁻¹ = E * Real.log y / (1 + η) := by
      field_simp
    have h4 : (1 - η) * E * Real.log y ≤ E * Real.log y / (1 + η) := by
      rw [le_div_iff₀ (by linarith)]
      have h5 : (1 - η) * (1 + η) ≤ 1 := by nlinarith
      have h6 : 0 < E * Real.log y := mul_pos hE0 hlog
      nlinarith
    rw [h3] at h2
    linarith
  -- the moment order
  have hpow : ∀ᶠ y : ℕ in atTop, (1 / 2 : ℝ) ^ (⌈Real.log y⌉₊) ≤ η := by
    have h1 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun y : ℕ => ⌈Real.log y⌉₊) atTop atTop :=
      tendsto_nat_ceil_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact (h1.comp h2).eventually (ge_mem_nhds hη0)
  rw [Filter.frequently_atTop]
  intro n₀
  have hbig := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop ((n₀ : ℝ) + 2))
  obtain ⟨y, hy⟩ := (hMert.and (hpow.and ((eventually_log_six_add_le hη0).and
    (hbig.and (eventually_ge_atTop 2))))).exists
  obtain ⟨hMy, hpy, hly, hby, hy2⟩ := hy
  simp only [Function.comp] at hby
  set m := ⌈Real.log y⌉₊ + 1 with hm
  set n := primorialPow y m with hn
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hmy : (m : ℝ) ≤ Real.log y + 2 := by
    rw [hm]; push_cast; have := Nat.ceil_lt_add_one hlogy.le; linarith
  have hmL : Real.log y + 1 ≤ m := by rw [hm]; push_cast; have := Nat.le_ceil (Real.log y); linarith
  -- n is large
  have h2n : 2 ^ m ≤ n := by
    rw [hn]; unfold primorialPow
    have h2mem : 2 ∈ (Finset.Icc 0 y).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hy2⟩, Nat.prime_two⟩
    rw [← Finset.mul_prod_erase _ _ h2mem]
    exact Nat.le_mul_of_pos_right _ (Finset.prod_pos fun p hp =>
      pow_pos (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2.pos m)
  have hmn : m < n := lt_of_lt_of_le Nat.lt_two_pow_self h2n
  have hn0 : (n₀ : ℝ) + 2 ≤ m := le_trans hby (by linarith)
  refine ⟨n, by exact_mod_cast (show n₀ ≤ n by
    have : (n₀ : ℝ) < n := by
      have : (m : ℝ) < n := by exact_mod_cast hmn
      linarith
    exact_mod_cast this.le), ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast primorialPow_pos y m
  have hn3 : (3 : ℝ) ≤ n := by
    have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
    have : (2 : ℝ) ≤ m := by linarith
    linarith
  have hlogn : 1 < Real.log n := by
    have := Real.add_one_le_exp 1
    have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    rw [← Real.exp_lt_exp, Real.exp_log hnpos]; linarith
  have hll0 : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlogn.le
  -- log log n ≤ (1 + η) log y
  have hlogn6 : Real.log n ≤ 6 * m * y := log_primorialPow_le y m
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hll : Real.log (Real.log n) ≤ (1 + η) * Real.log y := by
    have h1 : Real.log (Real.log n) ≤ Real.log (6 * m * y) :=
      Real.log_le_log (by linarith) hlogn6
    have h2 : Real.log (6 * m * y) = Real.log 6 + Real.log m + Real.log y := by
      rw [Real.log_mul (by positivity) hy0.ne', Real.log_mul (by norm_num) (by positivity)]
    have h3 : Real.log m ≤ Real.log (Real.log y + 2) :=
      Real.log_le_log (by positivity) hmy
    linarith
  -- σ(n)/n ≥ (1 − η)² E log y
  have hsig := sigma_div_primorialPow_ge y m (by omega)
  have hm1 : m - 1 = ⌈Real.log y⌉₊ := by omega
  rw [hm1] at hsig
  have hσ : (1 - η) ^ 2 * E * Real.log y ≤ ((sigma 1 n : ℕ) : ℝ) / n := by
    refine le_trans ?_ hsig
    have h1 : 0 ≤ 1 - (1 / 2 : ℝ) ^ ⌈Real.log y⌉₊ := by linarith
    calc (1 - η) ^ 2 * E * Real.log y = ((1 - η) * E * Real.log y) * (1 - η) := by ring
      _ ≤ (mertensPrimeProduct y)⁻¹ * (1 - (1 / 2 : ℝ) ^ ⌈Real.log y⌉₊) :=
          mul_le_mul hMy (by linarith) (by linarith) (inv_nonneg.mpr
            (mertensPrimeProduct_pos y).le)
  rw [le_div_iff₀ hnpos] at hσ
  by_cases hEε : E - ε ≤ 0
  · have : (E - ε) * n * Real.log (Real.log n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hEε hnpos.le) hll0
    exact this.trans (Nat.cast_nonneg _)
  push Not at hEε
  have hkey : (E - ε) * (1 + η) ≤ (1 - η) ^ 2 * E := by
    have h1 : (1 - 2 * η) * E ≤ (1 - η) ^ 2 * E := by
      apply mul_le_mul_of_nonneg_right _ hE0.le; nlinarith
    have h2 : η * E ≤ ε / 4 := by
      have := mul_le_mul_of_nonneg_right hηε hE0.le
      rw [show ε / (4 * E) * E = ε / 4 by field_simp] at this
      linarith
    nlinarith
  calc (E - ε) * n * Real.log (Real.log n) ≤ (E - ε) * n * ((1 + η) * Real.log y) :=
        mul_le_mul_of_nonneg_left hll (by positivity)
    _ = ((E - ε) * (1 + η)) * Real.log y * n := by ring
    _ ≤ (1 - η) ^ 2 * E * Real.log y * n := by gcongr
    _ ≤ ((sigma 1 n : ℕ) : ℝ) := hσ

/-! ## The defect criterion -/

/-- **The Mertens bound with the local defects.** With `x_p = p^{−(v_p(n)+1)}` for the primes
`p ≤ N`, `σ(n)/n ≤ (∏_{p≤N}(1 − 1/p))^{−1} e^{−Σ_{p≤N} x_p} (1 + 1/N)^{|S_{>N}|}`. -/
theorem sigma_div_le_mertens_defect {n N : ℕ} (hn : n ≠ 0) (hN : 1 ≤ N) :
    ((sigma 1 n : ℕ) : ℝ) / n ≤ (mertensPrimeProduct N)⁻¹ *
      Real.exp (-∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime, (1 / (p : ℝ)) ^ (n.factorization p + 1)) *
      (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card := by
  rw [sigma_div_eq_prod hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (· ≤ N)]
  have hpr : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfilt : n.primeFactors.filter (fun p => ¬ p ≤ N) = n.primeFactors.filter (N < ·) := by
    ext p; simp [not_le]
  rw [hfilt]
  set P := (Finset.Icc 0 N).filter Nat.Prime with hP
  set h : ℕ → ℝ := fun p => (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) / (1 - 1 / p) with hh
  have hsub : n.primeFactors.filter (· ≤ N) ⊆ P := fun p hp => by
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hp2⟩, hpr p hp1⟩
  have hext : ∏ p ∈ n.primeFactors.filter (· ≤ N), h p = ∏ p ∈ P, h p := by
    refine Finset.prod_subset hsub fun p hp hnot => ?_
    have hpp := (Finset.mem_filter.mp hp).2
    have hpN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hndvd : ¬ p ∣ n := fun hd => hnot (Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hpp, hd, hn⟩, hpN⟩)
    have hf : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hne : 1 - 1 / (p : ℝ) ≠ 0 := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
      linarith
    simp only [hh, hf, zero_add, pow_one]
    exact div_self hne
  have hsplit : ∏ p ∈ P, h p = (mertensPrimeProduct N)⁻¹ *
      ∏ p ∈ P, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) := by
    rw [inv_mertensPrimeProduct_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [hh]
    rw [div_eq_mul_inv, mul_comm]
  have hexp : ∏ p ∈ P, (1 - (1 / (p : ℝ)) ^ (n.factorization p + 1)) ≤
      Real.exp (-∑ p ∈ P, (1 / (p : ℝ)) ^ (n.factorization p + 1)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      have : (1 / (p : ℝ)) ^ (n.factorization p + 1) ≤ 1 :=
        pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; linarith)
      linarith
    · have := Real.add_one_le_exp (-(1 / (p : ℝ)) ^ (n.factorization p + 1))
      linarith
  have hM0 : 0 ≤ (mertensPrimeProduct N)⁻¹ := inv_nonneg.mpr (mertensPrimeProduct_pos N).le
  have h1 : ∏ p ∈ n.primeFactors.filter (· ≤ N), h p ≤ (mertensPrimeProduct N)⁻¹ *
      Real.exp (-∑ p ∈ P, (1 / (p : ℝ)) ^ (n.factorization p + 1)) := by
    rw [hext, hsplit]; exact mul_le_mul_of_nonneg_left hexp hM0
  have h2 : ∏ p ∈ n.primeFactors.filter (N < ·), h p ≤
      (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card :=
    (Finset.prod_le_prod (fun p hp => local_factor_nonneg (hpr p (Finset.mem_filter.mp hp).1))
      (fun p hp => local_factor_le (hpr p (Finset.mem_filter.mp hp).1))).trans (prod_inv_gt_le hN)
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun p hp =>
    local_factor_nonneg (hpr p (Finset.mem_filter.mp hp).1)) (by positivity)

/-- **Robin's inequality from a local defect.** For every `δ > 0`, eventually every `n` with
`Σ_{p ≤ ⌊log n⌋} p^{−(v_p(n)+1)} ≥ δ` satisfies `σ(n) < e^γ n log log n`. A prime `p ∤ n` contributes
`1/p` to the defect, a prime with `v_p(n) < k` contributes at least `p^{−k}`. -/
theorem eventually_sigma_lt_robin_of_defect {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, δ ≤ ∑ p ∈ (Finset.Icc 0 ⌊Real.log n⌋₊).filter Nat.Prime,
        (1 / (p : ℝ)) ^ (n.factorization p + 1) →
      ((sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  set q := Real.exp (-δ) with hq
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 < q := Real.exp_pos _
  set η := (1 - q) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  filter_upwards [eventually_sigma_div_le hη0] with n ⟨hn16, hll, hbound⟩ hdef
  have hn0 : n ≠ 0 := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN := two_le_floor_log hn16
  have hσ := sigma_div_le_mertens_defect hn0 (by omega : 1 ≤ ⌊Real.log n⌋₊)
  have hexp : Real.exp (-∑ p ∈ (Finset.Icc 0 ⌊Real.log n⌋₊).filter Nat.Prime,
      (1 / (p : ℝ)) ^ (n.factorization p + 1)) ≤ q := Real.exp_le_exp.mpr (by linarith)
  have hB0 : 0 ≤ (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^
      (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card := by positivity
  have hM0 : 0 ≤ (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ :=
    inv_nonneg.mpr (mertensPrimeProduct_pos _).le
  have hσ' : ((sigma 1 n : ℕ) : ℝ) / n ≤
      q * ((1 + η) ^ 2 * E * Real.log (Real.log n)) := by
    refine hσ.trans ?_
    calc (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ * Real.exp (-∑ p ∈ (Finset.Icc 0 ⌊Real.log n⌋₊).filter
          Nat.Prime, (1 / (p : ℝ)) ^ (n.factorization p + 1)) *
          (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card
        ≤ (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ * q *
          (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card := by
          gcongr
      _ = q * ((mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ *
          (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card) := by
          ring
      _ ≤ q * ((1 + η) ^ 2 * E * Real.log (Real.log n)) :=
          mul_le_mul_of_nonneg_left hbound hq0.le
  have hc : q * ((1 + η) ^ 2 * E) < E := by
    have h1 : q * (1 + η) ^ 2 < 1 := by
      have hη1 : η ≤ 1 / 4 := by rw [hη]; linarith
      have e : q * (1 + η) ^ 2 = q + q * η * (2 + η) := by ring
      have h2 : q * η * (2 + η) ≤ η * (9 / 4) := by
        have := mul_le_mul_of_nonneg_left (show 2 + η ≤ 9 / 4 by linarith) hη0.le
        nlinarith
      rw [e]
      have : η * (9 / 4) < 1 - q := by rw [hη]; nlinarith
      linarith
    have := mul_lt_mul_of_pos_right h1 hE0
    nlinarith
  rw [div_le_iff₀ hnr] at hσ'
  calc ((sigma 1 n : ℕ) : ℝ) ≤ q * ((1 + η) ^ 2 * E * Real.log (Real.log n)) * n := hσ'
    _ = (q * ((1 + η) ^ 2 * E)) * Real.log (Real.log n) * n := by ring
    _ < E * Real.log (Real.log n) * n := by
        apply mul_lt_mul_of_pos_right _ hnr
        exact mul_lt_mul_of_pos_right hc hll
    _ = E * n * Real.log (Real.log n) := by ring

end

end RHTower
