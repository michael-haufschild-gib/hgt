import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCoefficientMassOfAProducer

/-!
# Where the factor of two goes

A stencil with nonnegative increments `h = c * 1` is a sieve weight: its multiplicity is monotone,
and `h(p) = c(1)` at primes beyond the alphabet. Three facts locate the factor `2` of sieve parity.

* **The cones are disjoint.** A balanced stencil with `h ≥ 0` is zero. So the sieve cone (monotone
  multiplicity, mean value `V > 0`) never meets the producer cone (nonnegative multiplicity, `V = 0`).
  A producer must have negative increments, so the factor `2` is a property of the monotone cone.
* **The plain ledger.** `c(1) · #{K < p ≤ x} ≤ g(x) ≤ V x + Σ|c(k)|`.
* **The parity ledger.** All primes lie in `{λ = −1}`, and `1_{λ=−1} = (1 − λ)/2`, so
  `2 c(1) · #{K < p ≤ x} ≤ g(x) − Σ_k c(k) λ(k) L(⌊x/k⌋)`,  `L` the Liouville summatory function.

The factor `2` in the sieve bound is the term `Σ_k c(k) λ(k) L(⌊x/k⌋)`, a stencil read against
Liouville sums. A sieve cannot estimate it, because Type I data are blind to it. Any input that
bounds it removes the factor.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The mean value `V = D_c(1) = Σ c(k)/k` of the increment. -/
def meanValue (c : ℕ →₀ ℤ) : ℝ := ∑ k ∈ c.support, (c k : ℝ) / k

/-- The Liouville summatory function. -/
def liouvilleSum (N : ℕ) : ℤ := ∑ j ∈ Icc 1 N, ArithmeticFunction.liouville j

/-- The multiplicity is the partial sum of the increment. -/
theorem sum_Icc_increment (c : ℕ →₀ ℤ) (x : ℕ) :
    ∑ n ∈ Icc 1 x, increment c n = stepWeight c x := by
  induction x with
  | zero => simp
  | succ x ih => rw [Finset.sum_Icc_succ_top (by omega), ih, stepWeight_succ]

/-- **The plain main term.** `g(x) ≤ V x + Σ |c(k)|`. -/
theorem stepWeight_le_mean {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (x : ℕ) :
    (stepWeight c x : ℝ) ≤ meanValue c * x + coeffMass c := by
  rw [stepWeight, meanValue, coeffMass, sum_mul, ← sum_add_distrib, Int.cast_sum]
  refine sum_le_sum fun k hk => ?_
  rw [Int.cast_mul, Int.cast_natCast]
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hdiv : (k : ℝ) * ((x / k : ℕ) : ℝ) + ((x % k : ℕ) : ℝ) = x := by
    exact_mod_cast Nat.div_add_mod x k
  have hmod0 : (0 : ℝ) ≤ ((x % k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmod1 : ((x % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt x hk0).le
  have hq : ((x / k : ℕ) : ℝ) = (x : ℝ) / k - ((x % k : ℕ) : ℝ) / k := by
    field_simp
    linarith
  have hratio : |((x % k : ℕ) : ℝ) / k| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hkR]
    exact hmod1
  rw [hq]
  have h1 : (c k : ℝ) * ((x : ℝ) / k - ((x % k : ℕ) : ℝ) / k) =
      (c k : ℝ) / k * x + (-(c k : ℝ)) * (((x % k : ℕ) : ℝ) / k) := by ring
  rw [h1]
  have h2 : (-(c k : ℝ)) * (((x % k : ℕ) : ℝ) / k) ≤ |(c k : ℝ)| := by
    calc (-(c k : ℝ)) * (((x % k : ℕ) : ℝ) / k)
        ≤ |(-(c k : ℝ)) * (((x % k : ℕ) : ℝ) / k)| := le_abs_self _
      _ = |(c k : ℝ)| * |((x % k : ℕ) : ℝ) / k| := by rw [abs_mul, abs_neg]
      _ ≤ |(c k : ℝ)| * 1 := by gcongr
      _ = |(c k : ℝ)| := mul_one _
  linarith

/-- **The sieve cone and the producer cone are disjoint.** A balanced stencil with nonnegative
increments is zero. -/
theorem eq_zero_of_balanced_of_increment_nonneg {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c)
    (hinc : ∀ n, 0 < n → 0 ≤ increment c n) (k : ℕ) : c k = 0 := by
  have hmono : Monotone (stepWeight c) := by
    refine monotone_nat_of_le_succ fun r => ?_
    have := stepWeight_succ c r
    have := hinc (r + 1) (Nat.succ_pos r)
    omega
  have hLpos : 0 < IsProducer.period c := prod_pos fun k hk => Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have hzero : ∀ r, stepWeight c r = 0 := by
    intro r
    have h0 : stepWeight c ((r + 1) * IsProducer.period c) = 0 := by
      have h := stepWeight_periodic hc0 hbal (L := IsProducer.period c) IsProducer.dvd_period
        (r + 1) 0
      rwa [add_zero, stepWeight_zero] at h
    have hle : r ≤ (r + 1) * IsProducer.period c := by nlinarith
    have h1 := hmono hle
    have h2 := hmono (Nat.zero_le r)
    rw [stepWeight_zero] at h2
    omega
  have hinc0 : ∀ n, 0 < n → increment c n = 0 := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have := stepWeight_succ c j
    rw [hzero, hzero] at this
    omega
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hc0
  · rw [coeff_eq_moebius_increment c hk]
    refine sum_eq_zero fun x hx => ?_
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hb : 0 < x.2 := Nat.pos_of_ne_zero fun h => hn0 (by rw [← hprod, h, mul_zero])
    rw [hinc0 _ hb, mul_zero]

/-- A producer has a negative increment. -/
theorem IsProducer.exists_increment_neg {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) :
    ∃ n, 0 < n ∧ increment c n < 0 := by
  by_contra hno
  push Not at hno
  have h1 := eq_zero_of_balanced_of_increment_nonneg hP.zero hP.balanced hno 1
  have h2 := hP.le_coeff_one
  have h3 := hP.one_le_m
  rw [h1] at h2
  omega

/-- **The sieve mean value is positive.** A nonzero stencil with `h ≥ 0` has `V > 0`. -/
theorem meanValue_pos {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hinc : ∀ n, 0 < n → 0 ≤ increment c n)
    {k : ℕ} (hk : c k ≠ 0) : 0 < meanValue c := by
  by_contra hnot
  push Not at hnot
  rcases hnot.lt_or_eq with hneg | heq
  · -- A negative mean value drives the multiplicity below zero.
    obtain ⟨x, hx⟩ := exists_nat_gt ((coeffMass c + 1) / (-meanValue c))
    have hx' : coeffMass c + 1 < (x : ℝ) * (-meanValue c) := by
      rwa [div_lt_iff₀ (by linarith)] at hx
    have h1 := stepWeight_le_mean hc0 x
    have hg : (0 : ℝ) ≤ stepWeight c x := by
      have : 0 ≤ stepWeight c x := by
        rw [← sum_Icc_increment]
        exact sum_nonneg fun n hn => hinc n (mem_Icc.mp hn).1
      exact_mod_cast this
    nlinarith
  · exact hk (eq_zero_of_balanced_of_increment_nonneg hc0 heq hinc k)

/-- **The plain sieve ledger.** With `h ≥ 0` on an alphabet in `[1, K]`,
`c(1) · #{K < p ≤ x} ≤ g(x)`. -/
theorem coeff_one_mul_card_le {c : ℕ →₀ ℤ} {K : ℕ} (hK : AlphabetLE c K)
    (hinc : ∀ n, 0 < n → 0 ≤ increment c n) (x : ℕ) :
    c 1 * (((Ioc K x).filter Nat.Prime).card : ℤ) ≤ stepWeight c x := by
  classical
  rw [← sum_Icc_increment]
  have hsub : (Ioc K x).filter Nat.Prime ⊆ Icc 1 x := fun p hp => by
    obtain ⟨hI, hpr⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨hpr.pos, (mem_Ioc.mp hI).2⟩
  calc c 1 * (((Ioc K x).filter Nat.Prime).card : ℤ)
      = ∑ p ∈ (Ioc K x).filter Nat.Prime, increment c p := by
        rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
        refine sum_congr rfl fun p hp => ?_
        obtain ⟨hI, hpr⟩ := mem_filter.mp hp
        rw [increment_of_isRough (isRough_of_prime_of_alphabet hK hpr (mem_Ioc.mp hI).1)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hinc n (mem_Icc.mp hn).1

private lemma liouville_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ArithmeticFunction.liouville (a * b) =
      ArithmeticFunction.liouville a * ArithmeticFunction.liouville b := by
  rw [ArithmeticFunction.liouville_apply (mul_ne_zero ha hb),
    ArithmeticFunction.liouville_apply ha, ArithmeticFunction.liouville_apply hb,
    ArithmeticFunction.cardFactors_mul ha hb, pow_add]

private lemma liouville_eq_or {n : ℕ} (hn : n ≠ 0) :
    ArithmeticFunction.liouville n = 1 ∨ ArithmeticFunction.liouville n = -1 := by
  rw [ArithmeticFunction.liouville_apply hn]
  exact neg_one_pow_eq_or ℤ _

/-- Summing `λ` over multiples of `k`. -/
private lemma sum_Icc_dvd_liouville {k : ℕ} (hk : 0 < k) (x : ℕ) :
    ∑ n ∈ Icc 1 x, (if k ∣ n then ArithmeticFunction.liouville n else 0) =
      ArithmeticFunction.liouville k * liouvilleSum (x / k) := by
  induction x with
  | zero => simp [liouvilleSum]
  | succ x ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.succ_div]
    split_ifs with hd
    · obtain ⟨q, hq⟩ := hd
      have hq' : x / k + 1 = q := by
        have h1 : (x + 1) / k = q := by rw [hq]; exact Nat.mul_div_cancel_left q hk
        rw [Nat.succ_div, if_pos ⟨q, hq⟩] at h1
        exact h1
      have hq0 : q ≠ 0 := hq' ▸ Nat.succ_ne_zero _
      rw [hq', hq, liouville_mul hk.ne' hq0, liouvilleSum, liouvilleSum,
        ← hq', Finset.sum_Icc_succ_top (Nat.le_add_left 1 _), mul_add]
    · simp

/-- **The twist identity.** `Σ_{n ≤ x} λ(n) h(n) = Σ_k c(k) λ(k) L(⌊x/k⌋)`. -/
theorem sum_Icc_liouville_mul_increment {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (x : ℕ) :
    ∑ n ∈ Icc 1 x, ArithmeticFunction.liouville n * increment c n =
      ∑ k ∈ c.support, c k * (ArithmeticFunction.liouville k * liouvilleSum (x / k)) := by
  have hexp : ∀ n ∈ Icc 1 x, ArithmeticFunction.liouville n * increment c n =
      ∑ k ∈ c.support, c k * (if k ∣ n then ArithmeticFunction.liouville n else 0) := by
    intro n _
    rw [increment, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [sum_congr rfl hexp, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0
  rw [← mul_sum, sum_Icc_dvd_liouville hk0]

/-- **The parity ledger.** With `h ≥ 0` on an alphabet in `[1, K]`,
`2 c(1) · #{K < p ≤ x} ≤ g(x) − Σ_k c(k) λ(k) L(⌊x/k⌋)`. The factor `2` is paid by the last term. -/
theorem two_mul_coeff_one_mul_card_le {c : ℕ →₀ ℤ} {K : ℕ} (hc0 : c 0 = 0) (hK : AlphabetLE c K)
    (hinc : ∀ n, 0 < n → 0 ≤ increment c n) (x : ℕ) :
    2 * c 1 * (((Ioc K x).filter Nat.Prime).card : ℤ) ≤
      stepWeight c x -
        ∑ k ∈ c.support, c k * (ArithmeticFunction.liouville k * liouvilleSum (x / k)) := by
  classical
  rw [← sum_Icc_increment, ← sum_Icc_liouville_mul_increment hc0, ← sum_sub_distrib]
  have hsub : (Ioc K x).filter Nat.Prime ⊆ Icc 1 x := fun p hp => by
    obtain ⟨hI, hpr⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨hpr.pos, (mem_Ioc.mp hI).2⟩
  have hnonneg : ∀ n ∈ Icc 1 x, n ∉ (Ioc K x).filter Nat.Prime →
      0 ≤ increment c n - ArithmeticFunction.liouville n * increment c n := by
    intro n hn _
    have hn1 := (mem_Icc.mp hn).1
    have hh := hinc n hn1
    rcases liouville_eq_or (n := n) (by omega) with h | h <;> rw [h] <;> linarith
  calc 2 * c 1 * (((Ioc K x).filter Nat.Prime).card : ℤ)
      = ∑ p ∈ (Ioc K x).filter Nat.Prime,
          (increment c p - ArithmeticFunction.liouville p * increment c p) := by
        rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
        refine sum_congr rfl fun p hp => ?_
        obtain ⟨hI, hpr⟩ := mem_filter.mp hp
        rw [increment_of_isRough (isRough_of_prime_of_alphabet hK hpr (mem_Ioc.mp hI).1),
          ArithmeticFunction.liouville_apply hpr.ne_zero,
          ArithmeticFunction.cardFactors_apply_prime hpr]
        ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub hnonneg

/-- **The parity floor of the sieve.** For every `x ≥ 1`,
`2 c(1) #{K < p ≤ x} ≤ V x + Σ|c(k)| + Σ|c(k)| |L(⌊x/k⌋)|`. When the Liouville term is negligible this
is `V ≥ 2 c(1)/log x` up to lower order: the constant `2` is sharp exactly when `L` cancels. -/
theorem two_mul_card_le_mean {c : ℕ →₀ ℤ} {K : ℕ} (hc0 : c 0 = 0) (hK : AlphabetLE c K)
    (hinc : ∀ n, 0 < n → 0 ≤ increment c n) (x : ℕ) :
    2 * (c 1 : ℝ) * (((Ioc K x).filter Nat.Prime).card : ℝ) ≤
      meanValue c * x + coeffMass c +
        ∑ k ∈ c.support, |(c k : ℝ)| * |(liouvilleSum (x / k) : ℝ)| := by
  have h := two_mul_coeff_one_mul_card_le hc0 hK hinc x
  have hR : 2 * (c 1 : ℝ) * (((Ioc K x).filter Nat.Prime).card : ℝ) ≤
      (stepWeight c x : ℝ) - ∑ k ∈ c.support, (c k : ℝ) *
        ((ArithmeticFunction.liouville k : ℝ) * (liouvilleSum (x / k) : ℝ)) := by
    exact_mod_cast h
  have hbound : -∑ k ∈ c.support, (c k : ℝ) *
      ((ArithmeticFunction.liouville k : ℝ) * (liouvilleSum (x / k) : ℝ)) ≤
      ∑ k ∈ c.support, |(c k : ℝ)| * |(liouvilleSum (x / k) : ℝ)| := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun k hk => ?_
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hl : |((ArithmeticFunction.liouville k : ℤ) : ℝ)| = 1 := by
      rcases liouville_eq_or hk0 with h | h <;> rw [h] <;> simp
    calc -((c k : ℝ) * ((ArithmeticFunction.liouville k : ℝ) * (liouvilleSum (x / k) : ℝ)))
        ≤ |(c k : ℝ) * ((ArithmeticFunction.liouville k : ℝ) * (liouvilleSum (x / k) : ℝ))| :=
          neg_le_abs _
      _ = _ := by rw [abs_mul, abs_mul, hl, one_mul]
  linarith [stepWeight_le_mean hc0 x]

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
