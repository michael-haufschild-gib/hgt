import GaloisForLFunctions.BiScaleUncertainty.KerPCenteredSieveAndFirstSecondMomentReciprocity

/-!
# Pillar I: Pronic Bézout Splitting, Mixed-Difference Calculus, and Prime-Power Indecomposability (`PronicBezoutSplitAndPrimePowerIndecomposability`)

This module establishes **Pillar I** of **Bézout–Valuation Incidence Mechanics**
(`GaloisForLFunctions.BezoutValuationIncidence`), resolving **Wall 11 (Node Criticality:
Distinguishing `log 4` from `log 6`)** and **Wall 9 (The Beurling Obstruction)** at the foundational
algebraic level:

1. **Mixed Multiplicative Difference Annihilation of `log` vs. 1D Prime-Fiber Gradient
   (`mixedMulDiff_log_eq_zero`, `mulAxisDiff_log_eq_log`, `wall11_mixed_difference_log4_vs_log6`):**
   On the prime valuation complex $\mathbb{N}_0^{(\mathcal{P})}$, the 2D mixed multiplicative
   difference $\Delta_{d_1, d_2}^\times F(m) = F(d_1 d_2 m) - F(d_1 m) - F(d_2 m) + F(m)$
   annihilates $n \mapsto \log n$ identically for all $d_1, d_2, m \ge 1$ (so at $n = 6 = 2 \cdot 3$,
   $\Delta_{2, 3}^\times \log(1) = 0$), whereas along any single scale axis $d \ge 1$ (such as
   $n = 4 = 2^2$), $\Delta_2^\times \log(2) = \log 4 - \log 2 = \log 2 > 0$.

2. **Pronic Successor Coprimality, Unique Factor Recovery, and Divisor Bijection
   (`coprime_of_dvd_self_succ`, `gcd_mul_self_succ_eq`, `mul_injective_on_bezoutSuccessorPairSet`,
   `image_mul_bezoutSuccessorPairSet_eq_divisors`, `sum_divisors_pronicSeq_eq_sieveSeq_mul_succ`):**
   Because consecutive integers in $\mathbb{N}$ satisfy $\gcd(k, k + 1) = 1$ (which fails in
   Beurling generalized number systems), every pair of divisors $(d_1, d_2)$ with $d_1 \mid k$ and
   $d_2 \mid (k + 1)$ is automatically coprime ($\gcd(d_1, d_2) = 1$), and its factors are
   uniquely recovered from the product $n = d_1 d_2$ via $d_1 = \gcd(n, k)$ and
   $d_2 = \gcd(n, k + 1)$. Consequently, $(d_1, d_2) \mapsto d_1 d_2$ is a strict bijection from
   `bezoutSuccessorPairSet N k` onto `Nat.divisors (k(k + 1))` whenever $N \ge k + 1$.

3. **Prime-Power Indecomposability & Total Annihilation of Prime Powers on Centered Bézout Pairs
   (`not_isPrimePow_mul_of_coprime`, `vonMangoldt_mul_eq_zero_of_coprime`,
   `vonMangoldt_mul_eq_zero_of_mem_centeredBezoutSuccessorPairSet`,
   `wall11_four_excluded_six_attained`, `vonMangoldt_pronicSeq_eq_zero`):**
   In the centered successor product $\widetilde{s}_{N,c}(k)\,\widetilde{s}_{N,c}(k + 1)$
   (`d₁, d₂ ≥ 2`), every active pair $(d_1, d_2)$ satisfies $\gcd(d_1, d_2) = 1$ with
   $d_1, d_2 \ge 2$, so its product $n = d_1 d_2$ is **never** a prime power
   (`¬ IsPrimePow (d₁ * d₂)`) and satisfies $\Lambda(d_1 d_2) = 0$ identically. In particular,
   $n = 4 = 2^2$ is excluded from `centeredBezoutSuccessorPairSet N k` for all $N, k$, whereas
   $n = 6 = 2 \cdot 3$ is attained at $k = 2$, and $\Lambda(k(k + 1)) = 0$ for every $k \ge 2$.
-/

open Finset
open scoped BigOperators ArithmeticFunction

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Mixed Multiplicative Differences vs. 1D Prime-Axis Gradients (Wall 11) -/

/-- The pronic successor product `P(k) = k * (k + 1)`. -/
def pronicSeq (k : ℕ) : ℕ :=
  k * (k + 1)

/-- The truncated divisor sum (sieve polynomial response)
`s_{N,c}(k) = ∑_{d ∈ [1, N], d ∣ k} c(d)`. -/
def sieveSeq (N : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ k), c d

/-- The centered truncated divisor sum (excluding the trivial divisor `d = 1`):
`s̃_{N,c}(k) = ∑_{d ∈ [2, N], d ∣ k} c(d)`. -/
def centeredSieveSeq (N : ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 2 N).filter (fun d => d ∣ k), c d

/-- The set of divisor pairs `(d₁, d₂) ∈ [1, N]²` dividing `(k, k + 1)` respectively. -/
def bezoutSuccessorPairSet (N k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).filter (fun d => d ∣ k)) ×ˢ
    ((Finset.Icc 1 N).filter (fun d => d ∣ (k + 1)))

/-- The set of non-trivial divisor pairs `(d₁, d₂) ∈ [2, N]²` dividing `(k, k + 1)` respectively. -/
def centeredBezoutSuccessorPairSet (N k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 N).filter (fun d => d ∣ k)) ×ˢ
    ((Finset.Icc 2 N).filter (fun d => d ∣ (k + 1)))

/-- The 1D multiplicative difference along scale `d`:
`Δ_d^× F(m) = F(d * m) - F(m)`. -/
def mulAxisDiff (d : ℕ) (F : ℕ → ℝ) (m : ℕ) : ℝ :=
  F (d * m) - F m

/-- The 2D mixed multiplicative difference across two scales `d₁, d₂`:
`Δ_{d₁, d₂}^× F(m) = F(d₁ * d₂ * m) - F(d₁ * m) - F(d₂ * m) + F(m)`. -/
def mixedMulDiff (d₁ d₂ : ℕ) (F : ℕ → ℝ) (m : ℕ) : ℝ :=
  F (d₁ * d₂ * m) - F (d₁ * m) - F (d₂ * m) + F m

/-- **Mixed Multiplicative Difference Annihilation of `log` (`mixedMulDiff_log_eq_zero`):**
For all `d₁, d₂, m ≥ 1`, the 2D mixed multiplicative difference of `n ↦ log n` vanishes identically:
`log(d₁ d₂ m) - log(d₁ m) - log(d₂ m) + log m = 0`. -/
theorem mixedMulDiff_log_eq_zero {d₁ d₂ m : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hm : 1 ≤ m) :
    mixedMulDiff d₁ d₂ (fun n : ℕ => Real.log (n : ℝ)) m = 0 := by
  unfold mixedMulDiff
  have hd₁' : (d₁ : ℝ) ≠ 0 := by positivity
  have hd₂' : (d₂ : ℝ) ≠ 0 := by positivity
  have hm' : (m : ℝ) ≠ 0 := by positivity
  push_cast
  rw [Real.log_mul (mul_ne_zero hd₁' hd₂') hm', Real.log_mul hd₁' hd₂',
    Real.log_mul hd₁' hm', Real.log_mul hd₂' hm']
  ring

/-- **1D Prime-Axis Non-Vanishing Gradient of `log` (`mulAxisDiff_log_eq_log`):**
Along a single scale `d ≥ 1` at any node `m ≥ 1` (e.g. `d = 2, m = 2` for `4 = 2²`),
`Δ_d^× log(m) = log(d * m) - log m = log d`. -/
theorem mulAxisDiff_log_eq_log {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    mulAxisDiff d (fun n : ℕ => Real.log (n : ℝ)) m = Real.log (d : ℝ) := by
  unfold mulAxisDiff
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have hm' : (m : ℝ) ≠ 0 := by positivity
  push_cast
  rw [Real.log_mul hd' hm']
  ring

/-- **Concrete Wall 11 Mixed-Difference Separation (`log 4` vs `log 6`):**
At `n = 6 = 2 * 3`, the 2D mixed difference `mixedMulDiff 2 3 log 1` is `0`, whereas at
`n = 4 = 2 * 2`, the 1D dyadic difference `mulAxisDiff 2 log 2` is `log 2 > 0`. -/
theorem wall11_mixed_difference_log4_vs_log6 :
    mixedMulDiff 2 3 (fun n : ℕ => Real.log (n : ℝ)) 1 = 0 ∧
      mulAxisDiff 2 (fun n : ℕ => Real.log (n : ℝ)) 2 = Real.log 2 ∧
      0 < Real.log 2 := by
  refine ⟨mixedMulDiff_log_eq_zero (by omega) (by omega) (by omega),
    mulAxisDiff_log_eq_log (by omega) (by omega), Real.log_pos (by norm_num)⟩

/-! ## §2. Coprime Successor Splitting, Unique Factor Recovery, and Sieve Expansion -/

/-- Consecutive integers `k` and `k + 1` are always coprime. -/
theorem coprime_self_succ (k : ℕ) : Nat.Coprime k (k + 1) := by
  simp [Nat.coprime_self_add_right]

/-- Every pair `(d₁, d₂)` dividing `(k, k + 1)` is automatically coprime (`gcd(d₁, d₂) = 1`). -/
theorem coprime_of_dvd_self_succ {d₁ d₂ k : ℕ} (hd₁ : d₁ ∣ k) (hd₂ : d₂ ∣ (k + 1)) :
    Nat.Coprime d₁ d₂ :=
  (coprime_self_succ k).coprime_dvd_left hd₁ |>.coprime_dvd_right hd₂

/-- Every pair `(d₁, d₂) ∈ bezoutSuccessorPairSet N k` is coprime and its product divides `k(k + 1)`. -/
theorem coprime_and_mul_dvd_pronic_of_mem_bezoutSuccessorPairSet {N k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ bezoutSuccessorPairSet N k) :
    Nat.Coprime p.1 p.2 ∧ p.1 * p.2 ∣ pronicSeq k := by
  unfold bezoutSuccessorPairSet pronicSeq at *
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨coprime_of_dvd_self_succ hp.1.2 hp.2.2, mul_dvd_mul hp.1.2 hp.2.2⟩

/-- **Unique Recovery of Factors from Pronic Product:**
If `d₁ ∣ k` and `d₂ ∣ (k + 1)`, then `gcd(d₁ * d₂, k) = d₁` and `gcd(d₁ * d₂, k + 1) = d₂`. -/
theorem gcd_mul_self_succ_eq {d₁ d₂ k : ℕ} (hd₁ : d₁ ∣ k) (hd₂ : d₂ ∣ (k + 1)) :
    Nat.gcd (d₁ * d₂) k = d₁ ∧ Nat.gcd (d₁ * d₂) (k + 1) = d₂ := by
  have hcop_d₂_k : Nat.Coprime d₂ k :=
    ((coprime_self_succ k).symm.coprime_dvd_left hd₂)
  have hcop_d₁_k1 : Nat.Coprime d₁ (k + 1) :=
    (coprime_self_succ k).coprime_dvd_left hd₁
  constructor
  · rw [mul_comm d₁ d₂, hcop_d₂_k.gcd_mul_left_cancel d₁]
    exact Nat.gcd_eq_left hd₁
  · rw [hcop_d₁_k1.gcd_mul_left_cancel d₂]
    exact Nat.gcd_eq_left hd₂

/-- **Strict Injectivity of Pronic Factor Multiplication at Fixed `k`:**
At any fixed `k`, the multiplication map `(d₁, d₂) ↦ d₁ * d₂` is strictly injective on pairs
with `d₁ ∣ k` and `d₂ ∣ (k + 1)`. -/
theorem mul_injective_on_bezoutSuccessorPairSet (N k : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (bezoutSuccessorPairSet N k : Set (ℕ × ℕ)) := by
  intro p₁ hp₁ p₂ hp₂ hmul
  simp only [Finset.mem_coe, bezoutSuccessorPairSet, Finset.mem_product,
    Finset.mem_filter] at hp₁ hp₂
  have h1 := gcd_mul_self_succ_eq hp₁.1.2 hp₁.2.2
  have h2 := gcd_mul_self_succ_eq hp₂.1.2 hp₂.2.2
  dsimp at hmul
  ext
  · rw [← h1.1, hmul, h2.1]
  · rw [← h1.2, hmul, h2.2]

/-- `sieveSeq` agrees with `BiScaleUncertainty.sievedDivisorSum` for all `k ≥ 1`. -/
theorem sieveSeq_eq_sievedDivisorSum (N : ℕ) (c : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    sieveSeq N c k = GaloisForLFunctions.BiScaleUncertainty.sievedDivisorSum N c k := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨m, rfl⟩
  exact (GaloisForLFunctions.BiScaleUncertainty.sievedDivisorSum_succ_eq_sum_filter_Icc N c m).symm

/-- Splitting off the `d = 1` term from `sieveSeq N c k` yields `c 1 + centeredSieveSeq N c k`. -/
theorem sieveSeq_eq_c_one_add_centeredSieveSeq {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N c k = c 1 + centeredSieveSeq N c k := by
  unfold sieveSeq centeredSieveSeq
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (1 : ℕ) ∉ (Finset.Icc 2 N).filter (fun d => d ∣ k) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hIcc, Finset.filter_insert, if_pos (one_dvd k), Finset.sum_insert hnot]

/-- Product of `sieveSeq` at `k` and `k + 1` expands over `bezoutSuccessorPairSet N k`. -/
theorem sieveSeq_mul_succ_eq_sum_bezoutSuccessorPairSet (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N c k * sieveSeq N c (k + 1) =
      ∑ p ∈ bezoutSuccessorPairSet N k, c p.1 * c p.2 := by
  unfold sieveSeq bezoutSuccessorPairSet
  rw [Finset.sum_mul_sum, ← Finset.sum_product']

/-- Product of `centeredSieveSeq` at `k` and `k + 1` expands over `centeredBezoutSuccessorPairSet N k`. -/
theorem centeredSieveSeq_mul_succ_eq_sum_centeredBezoutSuccessorPairSet
    (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    centeredSieveSeq N c k * centeredSieveSeq N c (k + 1) =
      ∑ p ∈ centeredBezoutSuccessorPairSet N k, c p.1 * c p.2 := by
  unfold centeredSieveSeq centeredBezoutSuccessorPairSet
  rw [Finset.sum_mul_sum, ← Finset.sum_product']

/-! ## §3. Prime-Power Indecomposability & Pronic Divisor Bijection -/

/-- **Prime-Power Indecomposability under Coprime Factorization (`not_isPrimePow_mul_of_coprime`):**
No product `d₁ * d₂` of two coprime integers `d₁ ≥ 2` and `d₂ ≥ 2` can be a prime power. -/
theorem not_isPrimePow_mul_of_coprime {d₁ d₂ : ℕ} (hcop : Nat.Coprime d₁ d₂)
    (hd₁ : 2 ≤ d₁) (hd₂ : 2 ≤ d₂) :
    ¬ IsPrimePow (d₁ * d₂) := by
  intro hpp
  rw [isPrimePow_nat_iff] at hpp
  rcases hpp with ⟨p, m, hp, hm, hpm⟩
  obtain ⟨q₁, hq₁_prime, hq₁_dvd⟩ := Nat.exists_prime_and_dvd (by omega : d₁ ≠ 1)
  obtain ⟨q₂, hq₂_prime, hq₂_dvd⟩ := Nat.exists_prime_and_dvd (by omega : d₂ ≠ 1)
  have hq₁_pm : q₁ ∣ p ^ m := by
    rw [hpm]
    exact dvd_mul_of_dvd_left hq₁_dvd d₂
  have hq₂_pm : q₂ ∣ p ^ m := by
    rw [hpm]
    exact dvd_mul_of_dvd_right hq₂_dvd d₁
  have hq₁_p : q₁ ∣ p := hq₁_prime.dvd_of_dvd_pow hq₁_pm
  have hq₂_p : q₂ ∣ p := hq₂_prime.dvd_of_dvd_pow hq₂_pm
  have hq₁_eq : q₁ = p := (Nat.dvd_prime hp).mp hq₁_p |>.resolve_left hq₁_prime.ne_one
  have hq₂_eq : q₂ = p := (Nat.dvd_prime hp).mp hq₂_p |>.resolve_left hq₂_prime.ne_one
  rw [hq₁_eq] at hq₁_dvd
  rw [hq₂_eq] at hq₂_dvd
  have hp_gcd : p ∣ Nat.gcd d₁ d₂ := Nat.dvd_gcd hq₁_dvd hq₂_dvd
  rw [hcop.gcd_eq_one] at hp_gcd
  exact hp.not_dvd_one hp_gcd

/-- **Von Mangoldt Annihilation on Coprime Products (`vonMangoldt_mul_eq_zero_of_coprime`):**
For any coprime integers `d₁ ≥ 2` and `d₂ ≥ 2`, `Λ(d₁ * d₂) = 0` identically. -/
theorem vonMangoldt_mul_eq_zero_of_coprime {d₁ d₂ : ℕ} (hcop : Nat.Coprime d₁ d₂)
    (hd₁ : 2 ≤ d₁) (hd₂ : 2 ≤ d₂) :
    ArithmeticFunction.vonMangoldt (d₁ * d₂) = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  exact not_isPrimePow_mul_of_coprime hcop hd₁ hd₂

/-- **Wall 11 Resolution — Total Annihilation of Prime Powers on Centered Bézout Pairs:**
Every pair `(d₁, d₂) ∈ centeredBezoutSuccessorPairSet N k` has `¬ IsPrimePow (d₁ * d₂)` and
`Λ(d₁ * d₂) = 0`. -/
theorem vonMangoldt_mul_eq_zero_of_mem_centeredBezoutSuccessorPairSet {N k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ centeredBezoutSuccessorPairSet N k) :
    ¬ IsPrimePow (p.1 * p.2) ∧ ArithmeticFunction.vonMangoldt (p.1 * p.2) = 0 := by
  unfold centeredBezoutSuccessorPairSet at hp
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
  have hcop : Nat.Coprime p.1 p.2 := coprime_of_dvd_self_succ hp.1.2 hp.2.2
  exact ⟨not_isPrimePow_mul_of_coprime hcop hp.1.1.1 hp.2.1.1,
    vonMangoldt_mul_eq_zero_of_coprime hcop hp.1.1.1 hp.2.1.1⟩

/-- **Wall 11 Concrete Separation (`4 = 2²` vs `6 = 2 · 3`):**
For every `N k : ℕ`, `4 = 2²` is NEVER the product of any pair in
`centeredBezoutSuccessorPairSet N k`, whereas for all `N ≥ 3`, `(2, 3)` belongs to
`centeredBezoutSuccessorPairSet N 2` with product `2 * 3 = 6`. -/
theorem wall11_four_excluded_six_attained (N k : ℕ) :
    (∀ p ∈ centeredBezoutSuccessorPairSet N k, p.1 * p.2 ≠ 4) ∧
      (3 ≤ N → (2, 3) ∈ centeredBezoutSuccessorPairSet N 2 ∧ (2 : ℕ) * 3 = 6) := by
  constructor
  · intro p hp h4
    have hnot := (vonMangoldt_mul_eq_zero_of_mem_centeredBezoutSuccessorPairSet hp).1
    rw [h4] at hnot
    apply hnot
    rw [isPrimePow_nat_iff]
    exact ⟨2, 2, Nat.prime_two, by omega, by norm_num⟩
  · intro hN
    refine ⟨?_, rfl⟩
    unfold centeredBezoutSuccessorPairSet
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, by omega⟩, dvd_refl 2⟩, ⟨⟨by omega, hN⟩, dvd_refl 3⟩⟩

/-- **Universal Vanishing of `Λ(k(k + 1))` for `k ≥ 2` (`vonMangoldt_pronicSeq_eq_zero`):**
Every pronic number `k(k + 1)` with `k ≥ 2` is a product of two coprime integers `≥ 2`, so
`Λ(k(k + 1)) = 0` unconditionally for all `k ≥ 2` (while `Λ(pronicSeq 1) = Λ(2) = log 2`). -/
theorem vonMangoldt_pronicSeq_eq_zero {k : ℕ} (hk : 2 ≤ k) :
    ArithmeticFunction.vonMangoldt (pronicSeq k) = 0 := by
  unfold pronicSeq
  exact vonMangoldt_mul_eq_zero_of_coprime (coprime_self_succ k) hk (by omega)

/-- At `k = 1`, `Λ(pronicSeq 1) = Λ(2) = log 2`. -/
theorem vonMangoldt_pronicSeq_one :
    ArithmeticFunction.vonMangoldt (pronicSeq 1) = Real.log 2 := by
  change ArithmeticFunction.vonMangoldt 2 = Real.log 2
  exact ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two

/-- **Exact Pronic Divisor Bijection (`image_mul_bezoutSuccessorPairSet_eq_divisors`):**
For every `k ≥ 1` and `N ≥ k + 1`, the multiplication map `(d₁, d₂) ↦ d₁ * d₂` maps
`bezoutSuccessorPairSet N k` bijectively onto `Nat.divisors (k * (k + 1))`. -/
theorem image_mul_bezoutSuccessorPairSet_eq_divisors {N k : ℕ} (hk : 1 ≤ k) (hN : k + 1 ≤ N) :
    (bezoutSuccessorPairSet N k).image (fun p : ℕ × ℕ => p.1 * p.2) =
      Nat.divisors (pronicSeq k) := by
  ext n
  simp only [Finset.mem_image, bezoutSuccessorPairSet, Finset.mem_product,
    Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, pronicSeq]
  constructor
  · rintro ⟨⟨d₁, d₂⟩, ⟨⟨_, hd₁_dvd⟩, ⟨_, hd₂_dvd⟩⟩, rfl⟩
    exact ⟨mul_dvd_mul hd₁_dvd hd₂_dvd, by positivity⟩
  · rintro ⟨hdvd, _⟩
    rw [Nat.dvd_mul] at hdvd
    rcases hdvd with ⟨d₁, d₂, hd₁_dvd, hd₂_dvd, hmul⟩
    have hd₁_pos : 1 ≤ d₁ := Nat.pos_of_dvd_of_pos hd₁_dvd hk
    have hd₁_le : d₁ ≤ N := le_trans (Nat.le_of_dvd hk hd₁_dvd) (by omega)
    have hd₂_pos : 1 ≤ d₂ := Nat.pos_of_dvd_of_pos hd₂_dvd (by omega)
    have hd₂_le : d₂ ≤ N := le_trans (Nat.le_of_dvd (by omega) hd₂_dvd) hN
    exact ⟨(d₁, d₂), ⟨⟨⟨hd₁_pos, hd₁_le⟩, hd₁_dvd⟩, ⟨⟨hd₂_pos, hd₂_le⟩, hd₂_dvd⟩⟩, hmul⟩

/-- **Exact Pronic Divisor Sum Decomposition (`sum_divisors_pronicSeq_eq_sum_bezoutSuccessorPairSet`):**
For any `k ≥ 1`, `N ≥ k + 1`, and any function `F : ℕ → ℝ`,
`∑ n ∈ Nat.divisors (k(k + 1)), F n = ∑ p ∈ bezoutSuccessorPairSet N k, F (p.1 * p.2)`. -/
theorem sum_divisors_pronicSeq_eq_sum_bezoutSuccessorPairSet {N k : ℕ}
    (hk : 1 ≤ k) (hN : k + 1 ≤ N) (F : ℕ → ℝ) :
    (∑ n ∈ Nat.divisors (pronicSeq k), F n) =
      ∑ p ∈ bezoutSuccessorPairSet N k, F (p.1 * p.2) := by
  rw [← image_mul_bezoutSuccessorPairSet_eq_divisors hk hN,
    Finset.sum_image (mul_injective_on_bezoutSuccessorPairSet N k)]

/-- **Multiplicative Pronic Splitting Identity (`sum_divisors_pronicSeq_eq_sieveSeq_mul_succ`):**
For any `k ≥ 1`, `N ≥ k + 1`, and any function `F : ℕ → ℝ` multiplicative on coprime pairs
(`∀ d₁ d₂, Nat.Coprime d₁ d₂ → F (d₁ * d₂) = F d₁ * F d₂`),
`∑ n ∈ Nat.divisors (k(k + 1)), F n = sieveSeq N F k * sieveSeq N F (k + 1)`. -/
theorem sum_divisors_pronicSeq_eq_sieveSeq_mul_succ {N k : ℕ}
    (hk : 1 ≤ k) (hN : k + 1 ≤ N) {F : ℕ → ℝ}
    (hmul : ∀ d₁ d₂ : ℕ, Nat.Coprime d₁ d₂ → F (d₁ * d₂) = F d₁ * F d₂) :
    (∑ n ∈ Nat.divisors (pronicSeq k), F n) =
      sieveSeq N F k * sieveSeq N F (k + 1) := by
  rw [sum_divisors_pronicSeq_eq_sum_bezoutSuccessorPairSet hk hN F,
    sieveSeq_mul_succ_eq_sum_bezoutSuccessorPairSet]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact hmul p.1 p.2 (coprime_and_mul_dvd_pronic_of_mem_bezoutSuccessorPairSet hp).1

end
end GaloisForLFunctions.BezoutValuationIncidence
