import GaloisForLFunctions.BezoutValuationIncidence.PronicBezoutSplitAndPrimePowerIndecomposability

/-!
# Pillar II: Quotient-Dual Octave Reciprocity, LCM Fibre Parity Collapse, and `2`-Adic Valuation Switching (`QuotientDualOctaveReciprocityAndValuationSwitching`)

This module establishes **Pillar II** of **Bézout–Valuation Incidence Mechanics**
(`GaloisForLFunctions.BezoutValuationIncidence`), crossing the $\theta = 1$ polynomial-length
horizon ($k > N$) via **Quotient-Dual Octave Reciprocity** and proving the **$2$-Adic Valuation
Switching Law** between the $v_2(k) = 1$ ($\log 6$) and $v_2(k) = 2$ ($\log 4$) sectors:

1. **High-Divisor Complement & First Trans-Horizon Octave Reciprocity ($N + 1 \le k \le 2N$):**
   Because $\sum_{d \mid k} \mu(d) = 0$ for all $k \ge 2$, the truncated Möbius sieve sum satisfies
   `sieveSeq N moebiusReal k = - ∑_{d ∣ k, N < d} μ(d)` (`sieveSeq_moebiusReal_eq_neg_sum_gt`).
   On the first trans-horizon octave $k \in [N + 1, 2N]$, the only divisor of $k$ exceeding $N$ is
   $k$ itself (`divisors_filter_gt_eq_singleton_of_first_octave`), yielding the exact identities:
   - `sieveSeq_moebiusReal_first_octave`: $s_{N,\mu}(k) = -\mu(k)$,
   - `sieveSeq_moebiusReal_sq_first_octave`: $s_{N,\mu}(k)^2 = \mu(k)^2$,
   - `sieveSeq_moebiusReal_mul_succ_first_octave`: $s_{N,\mu}(k)s_{N,\mu}(k + 1) = \mu(k)\mu(k + 1)$.

2. **Trans-Horizon LCM Fibre Parity Collapse (`sievedLcmFibre_moebius_first_octave`):**
   Combining the Möbius LCM fibre inversion $F_{N,\mu}(L) = \mu(L) + \sum_{d \mid L, N < d} \mu(L/d)s_{N,\mu}(d)^2$
   with first-octave reciprocity proves that for every $L \in [N + 1, 2N]$:
   $$F_{N,\mu}(L) = \mu(L) + \mu(L)^2 \ge 0,$$
   which vanishes identically on all primes $p \in [N + 1, 2N]$
   (`sievedLcmFibre_moebius_prime_first_octave_eq_zero`), all odd-parity squarefree integers
   ($\mu(L) = -1$), and all non-squarefree integers ($\mu(L) = 0$), while equaling $+2$ on
   even-parity squarefree composites ($\mu(L) = +1$).

3. **Logarithmic Von Mangoldt First-Octave Split & Prime Annihilation
   (`truncLogMoebiusSum_first_octave`, `truncLogMoebiusSum_prime_first_octave_eq_zero`):**
   On $k \in [N + 1, 2N]$, $\Lambda_N(k) = -\sum_{d \mid k, d \le N} \mu(d)\log d = \Lambda(k) + \mu(k)\log k$,
   which vanishes identically on every prime $p \in [N + 1, 2N]$.

4. **Second Trans-Horizon Octave ($2N + 1 \le k \le 3N$) & `2`-Adic Valuation Switching (Wall 11):**
   On $k \in [2N + 1, 3N]$, only the dual quotients $m \in \{1, 2\}$ contribute
   (`sieveSeq_moebiusReal_second_octave`):
   $$s_{N,\mu}(k) = -\mu(k) - \mathbf{1}_{2 \mid k}\,\mu(k / 2).$$
   - **Total Annihilation of $v_2(k) = 1$ (`sieveSeq_moebiusReal_second_octave_two_mul_odd_eq_zero`):**
     For every odd $u$ with $2u \in [2N + 1, 3N]$ (the $\log 6 = \log(2 \cdot 3)$ sector),
     $s_{N,\mu}(2u) = -\mu(2u) - \mu(u) = 0$ identically!
   - **Activation of $v_2(k) = 2$ (`sieveSeq_moebiusReal_second_octave_four_mul_odd`):**
     For every odd $u$ with $4u \in [2N + 1, 3N]$ (the $\log 4 = \log(2^2)$ sector), while
     $\mu(4u) = 0$, $s_{N,\mu}(4u) = \mu(u)$!
-/

open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. High-Divisor Complement & First Trans-Horizon Octave Reciprocity -/

/-- Real-valued Möbius function `d ↦ (μ(d) : ℝ)`. -/
def moebiusReal (d : ℕ) : ℝ :=
  ((μ d : ℤ) : ℝ)

/-- The `R`-octave dual Möbius operator
`𝓜_R(k) = - ∑_{m ∈ [1, R], m ∣ k} μ(k / m)`. -/
def dualMoebiusOctaveSum (R k : ℕ) : ℝ :=
  - ∑ m ∈ (Finset.Icc 1 R).filter (fun m => m ∣ k), moebiusReal (k / m)

/-- The truncated logarithmic Möbius sieve approximant to von Mangoldt:
`Λ_N(k) = - ∑_{d ∈ [1, N], d ∣ k} μ(d) log d`. -/
def truncLogMoebiusSum (N k : ℕ) : ℝ :=
  - ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ k), moebiusReal d * Real.log (d : ℝ)

/-- For any `k ≥ 1`, `(Finset.Icc 1 N).filter (· ∣ k)` equals `k.divisors.filter (· ≤ N)`. -/
theorem filter_dvd_Icc_eq_divisors_filter_le (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (Finset.Icc 1 N).filter (fun d => d ∣ k) = k.divisors.filter (fun d => d ≤ N) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_, hdN⟩, hdk⟩
    exact ⟨⟨hdk, by omega⟩, hdN⟩
  · rintro ⟨⟨hdk, _⟩, hdN⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdk hk, hdN⟩, hdk⟩

/-- Full divisor sum of `moebiusReal` vanishes for all `k ≥ 2`. -/
theorem sum_divisors_moebiusReal_eq_zero {k : ℕ} (hk : 2 ≤ k) :
    ∑ d ∈ k.divisors, moebiusReal d = 0 := by
  unfold moebiusReal
  have h := congrArg (fun f : ArithmeticFunction ℝ => f k) (coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [coe_mul_zeta_apply, one_apply, if_neg (by omega : k ≠ 1)] at h
  exact h

/-- **Exact High-Divisor Complement Formula (`sieveSeq_moebiusReal_eq_neg_sum_gt`):**
For every `N : ℕ` and `k ≥ 2`, the truncated Möbius divisor sum `sieveSeq N moebiusReal k` equals
the negative of the sum of `μ(d)` over divisors `d ∣ k` strictly exceeding `N`. -/
theorem sieveSeq_moebiusReal_eq_neg_sum_gt (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    sieveSeq N moebiusReal k =
      - ∑ d ∈ k.divisors.filter (fun d => N < d), moebiusReal d := by
  unfold sieveSeq
  rw [filter_dvd_Icc_eq_divisors_filter_le N (by omega)]
  have hsplit := (Finset.sum_filter_add_sum_filter_not k.divisors (fun d => d ≤ N) moebiusReal).symm
  have hnot : k.divisors.filter (fun d => ¬ d ≤ N) = k.divisors.filter (fun d => N < d) := by
    ext d
    simp only [Finset.mem_filter, not_le]
  rw [hnot] at hsplit
  have hzero := sum_divisors_moebiusReal_eq_zero hk
  linarith

/-- **First Trans-Horizon Octave Divisor Collapse (`divisors_filter_gt_eq_singleton_of_first_octave`):**
For every `k ∈ [N + 1, 2N]`, the only divisor of `k` strictly exceeding `N` is `k` itself. -/
theorem divisors_filter_gt_eq_singleton_of_first_octave {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k ≤ 2 * N) :
    k.divisors.filter (fun d => N < d) = {k} := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨m, rfl⟩, hk0⟩, hdN⟩
    rcases m with _ | _ | m
    · simp at hk0
    · ring
    · exfalso
      nlinarith
  · intro hdk
    subst hdk
    exact ⟨⟨dvd_refl d, by omega⟩, by omega⟩

/-- **First Trans-Horizon Octave Möbius Reciprocity (`sieveSeq_moebiusReal_first_octave`):**
For every `N : ℕ` and `k ∈ [N + 1, 2N]`, `sieveSeq N moebiusReal k = -μ(k)`. -/
theorem sieveSeq_moebiusReal_first_octave {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k ≤ 2 * N) :
    sieveSeq N moebiusReal k = - moebiusReal k := by
  have hk_ge2 : 2 ≤ k := by omega
  rw [sieveSeq_moebiusReal_eq_neg_sum_gt N hk_ge2,
    divisors_filter_gt_eq_singleton_of_first_octave hk1 hk2, Finset.sum_singleton]

/-- In the first trans-horizon octave `k ∈ [N + 1, 2N]`, the squared sieve response equals `μ(k)²`. -/
theorem sieveSeq_moebiusReal_sq_first_octave {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k ≤ 2 * N) :
    sieveSeq N moebiusReal k ^ (2 : ℕ) = moebiusReal k ^ (2 : ℕ) := by
  rw [sieveSeq_moebiusReal_first_octave hk1 hk2, neg_sq]

/-- In the first trans-horizon octave `k ∈ [N + 1, 2N - 1]`, the successor correlation
`s_{N,μ}(k) s_{N,μ}(k + 1)` equals `μ(k) μ(k + 1)`. -/
theorem sieveSeq_moebiusReal_mul_succ_first_octave {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k + 1 ≤ 2 * N) :
    sieveSeq N moebiusReal k * sieveSeq N moebiusReal (k + 1) =
      moebiusReal k * moebiusReal (k + 1) := by
  rw [sieveSeq_moebiusReal_first_octave hk1 (by omega),
    sieveSeq_moebiusReal_first_octave (by omega) hk2, neg_mul_neg]

/-! ## §2. Trans-Horizon LCM Fibre Parity Collapse & Logarithmic First-Octave Split -/

/-- **Trans-Horizon LCM Fibre Parity Collapse (`sievedLcmFibre_moebius_first_octave`):**
For every `L ∈ [N + 1, 2N]`, the signed Möbius LCM fibre `sievedLcmFibre N μ L` collapses to
`μ(L) + μ(L)²`, which is non-negative (`≥ 0`), vanishes on all odd-parity squarefree integers
(`μ(L) = -1`, including all primes `p ∈ [N + 1, 2N]`) and all non-squarefree integers
(`μ(L) = 0`, including multiples of `4`), and equals `2` on even-parity squarefree composites
(`μ(L) = 1`). -/
theorem sievedLcmFibre_moebius_first_octave {N L : ℕ}
    (hL1 : N + 1 ≤ L) (hL2 : L ≤ 2 * N) :
    GaloisForLFunctions.BiScaleUncertainty.sievedLcmFibre N moebiusReal L =
      moebiusReal L + moebiusReal L ^ (2 : ℕ) := by
  have hN : 1 ≤ N := by omega
  have hLpos : 0 < L := by omega
  have h := GaloisForLFunctions.BiScaleUncertainty.sievedLcmFibre_moebius_eq_moebius_add_gt_divisors
    (N := N) (L := L) hN hLpos
  change GaloisForLFunctions.BiScaleUncertainty.sievedLcmFibre N moebiusReal L =
    moebiusReal L + ∑ d ∈ L.divisors.filter (fun d => N < d),
      moebiusReal (L / d) *
        GaloisForLFunctions.BiScaleUncertainty.sievedDivisorSum N moebiusReal d ^ (2 : ℕ) at h
  rw [h, divisors_filter_gt_eq_singleton_of_first_octave hL1 hL2, Finset.sum_singleton,
    Nat.div_self hLpos, ← sieveSeq_eq_sievedDivisorSum N moebiusReal (by omega : 1 ≤ L),
    sieveSeq_moebiusReal_sq_first_octave hL1 hL2]
  have hmu1 : moebiusReal 1 = 1 := by
    unfold moebiusReal
    simp
  rw [hmu1, one_mul]

/-- Every prime `p ∈ [N + 1, 2N]` has `sievedLcmFibre N moebiusReal p = 0` identically. -/
theorem sievedLcmFibre_moebius_prime_first_octave_eq_zero {N p : ℕ}
    (hp : Nat.Prime p) (hp1 : N + 1 ≤ p) (hp2 : p ≤ 2 * N) :
    GaloisForLFunctions.BiScaleUncertainty.sievedLcmFibre N moebiusReal p = 0 := by
  rw [sievedLcmFibre_moebius_first_octave hp1 hp2]
  have hmup : moebiusReal p = -1 := by
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  rw [hmup]
  ring

/-- **Logarithmic Von Mangoldt First-Octave Split (`truncLogMoebiusSum_first_octave`):**
For every `k ∈ [N + 1, 2N]`, `truncLogMoebiusSum N k = Λ(k) + μ(k) log k`. -/
theorem truncLogMoebiusSum_first_octave {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k ≤ 2 * N) :
    truncLogMoebiusSum N k =
      ArithmeticFunction.vonMangoldt k + moebiusReal k * Real.log (k : ℝ) := by
  have hk_gt1 : 1 < k := by omega
  unfold truncLogMoebiusSum
  rw [filter_dvd_Icc_eq_divisors_filter_le N (by omega)]
  have hsplit := (Finset.sum_filter_add_sum_filter_not k.divisors (fun d => d ≤ N)
    (fun d => moebiusReal d * Real.log (d : ℝ))).symm
  have hnot : k.divisors.filter (fun d => ¬ d ≤ N) = k.divisors.filter (fun d => N < d) := by
    ext d
    simp only [Finset.mem_filter, not_le]
  rw [hnot, divisors_filter_gt_eq_singleton_of_first_octave hk1 hk2, Finset.sum_singleton] at hsplit
  have hfull : ∑ d ∈ k.divisors, moebiusReal d * Real.log (d : ℝ) =
      - ArithmeticFunction.vonMangoldt k :=
    RHTower.Sieve.sum_moebius_mul_log_eq_neg_vonMangoldt hk_gt1
  linarith

/-- **Total Annihilation of Primes in `truncLogMoebiusSum` on `[N + 1, 2N]`:**
For every prime `p ∈ [N + 1, 2N]`, `truncLogMoebiusSum N p = 0` identically. -/
theorem truncLogMoebiusSum_prime_first_octave_eq_zero {N p : ℕ}
    (hp : Nat.Prime p) (hp1 : N + 1 ≤ p) (hp2 : p ≤ 2 * N) :
    truncLogMoebiusSum N p = 0 := by
  rw [truncLogMoebiusSum_first_octave hp1 hp2, ArithmeticFunction.vonMangoldt_apply_prime hp]
  unfold moebiusReal
  rw [ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-! ## §3. Second Trans-Horizon Octave (`2N + 1 ≤ k ≤ 3N`) & `2`-Adic Valuation Switching -/

/-- **Second Trans-Horizon Octave Reciprocity (`2N + 1 ≤ k ≤ 3N`):**
For every `k ∈ [2N + 1, 3N]`, a divisor `d ∣ k` satisfies `d > N` iff `d = k` or (`2 ∣ k` and `d = k / 2`),
so `sieveSeq N moebiusReal k = -μ(k) - (if 2 ∣ k then μ(k / 2) else 0)`. -/
theorem sieveSeq_moebiusReal_second_octave {N k : ℕ}
    (hk1 : 2 * N + 1 ≤ k) (hk2 : k ≤ 3 * N) :
    sieveSeq N moebiusReal k =
      - moebiusReal k - (if 2 ∣ k then moebiusReal (k / 2) else 0) := by
  have hk_ge2 : 2 ≤ k := by omega
  rw [sieveSeq_moebiusReal_eq_neg_sum_gt N hk_ge2]
  by_cases h2 : 2 ∣ k
  · rw [if_pos h2]
    have hset : k.divisors.filter (fun d => N < d) = {k, k / 2} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨m, hkm⟩, hk0⟩, hdN⟩
        rcases m with _ | _ | _ | m
        · omega
        · left; omega
        · right; omega
        · exfalso; nlinarith
      · rintro (hdk | hdk2)
        · subst hdk
          exact ⟨⟨dvd_refl d, by omega⟩, by omega⟩
        · subst hdk2
          exact ⟨⟨Nat.div_dvd_of_dvd h2, by omega⟩, by omega⟩
    have hne : k ≠ k / 2 := by omega
    rw [hset, Finset.sum_pair hne]
    ring
  · rw [if_neg h2]
    have hset : k.divisors.filter (fun d => N < d) = {k} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨m, hkm⟩, hk0⟩, hdN⟩
        rcases m with _ | _ | _ | m
        · omega
        · omega
        · exfalso
          apply h2
          exact ⟨d, by omega⟩
        · exfalso; nlinarith
      · intro hdk
        subst hdk
        exact ⟨⟨dvd_refl d, by omega⟩, by omega⟩
    rw [hset, Finset.sum_singleton]
    ring

/-- **`2`-Adic Valuation Switching in the Second Octave — Annihilation of `2 ∥ k` (`log 6` Sector):**
For every odd integer `u` (`Nat.Coprime 2 u`) such that `2u ∈ [2N + 1, 3N]`,
`sieveSeq N moebiusReal (2 * u) = 0` identically! -/
theorem sieveSeq_moebiusReal_second_octave_two_mul_odd_eq_zero {N u : ℕ}
    (hodd : Nat.Coprime 2 u) (hk1 : 2 * N + 1 ≤ 2 * u) (hk2 : 2 * u ≤ 3 * N) :
    sieveSeq N moebiusReal (2 * u) = 0 := by
  rw [sieveSeq_moebiusReal_second_octave hk1 hk2, if_pos (dvd_mul_right 2 u),
    Nat.mul_div_cancel_left u (by omega : 0 < 2)]
  unfold moebiusReal
  have hmul : μ (2 * u) = μ 2 * μ u :=
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hodd
  rw [hmul, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast
  ring

/-- **`2`-Adic Valuation Switching in the Second Octave — Activation of `4 ∣ k` (`log 4` Sector):**
For every odd integer `u` (`Nat.Coprime 2 u`) such that `4u ∈ [2N + 1, 3N]`, while `μ(4u) = 0`,
`sieveSeq N moebiusReal (4 * u) = μ(u)`! -/
theorem sieveSeq_moebiusReal_second_octave_four_mul_odd {N u : ℕ}
    (hodd : Nat.Coprime 2 u) (hk1 : 2 * N + 1 ≤ 4 * u) (hk2 : 4 * u ≤ 3 * N) :
    moebiusReal (4 * u) = 0 ∧ sieveSeq N moebiusReal (4 * u) = moebiusReal u := by
  have hnot_sqfree : ¬ Squarefree (4 * u) := by
    intro hsq
    have h4 : Squarefree 4 := hsq.squarefree_of_dvd (dvd_mul_right 4 u)
    exact absurd (h4 2 (by norm_num : 2 * 2 ∣ 4)) (by decide)
  have hmu4u : moebiusReal (4 * u) = 0 := by
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_sqfree]
    norm_num
  refine ⟨hmu4u, ?_⟩
  have h2dvd : 2 ∣ 4 * u := ⟨2 * u, by ring⟩
  have hdiv : 4 * u / 2 = 2 * u := by omega
  rw [sieveSeq_moebiusReal_second_octave hk1 hk2, hmu4u, if_pos h2dvd, hdiv]
  unfold moebiusReal
  have hmul : μ (2 * u) = μ 2 * μ u :=
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hodd
  rw [hmul, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
