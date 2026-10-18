import GaloisForLFunctions.TransHorizonIncidenceMechanics.DownwardBuchstabL2TelescopeAndSawtoothCoupling

/-!
# Pillar XXVI: Composite Squarefree Horizon Steps, Two-Band Parity Dichotomy, and Multi-Octave `L²` Energy Evaluation (`CompositeSquarefreeStepAndMultiOctaveL2Energy`)

## 1. Classical Baseline & Honest Classification (`README.md` §2)

- **Closest existing results:**
  - Buchstab's identity for truncated divisor sums $s_{n+1,c}(k) - s_{n,c}(k) = c(n+1)\mathbf{1}_{n+1 \mid k}$;
  - Möbius inversion $\sum_{d \mid k} \mu(d) = \mathbf{1}_{k=1}$;
  - Prime-horizon step identity $\mathcal{E}_p(M; \mu) - \mathcal{E}_{p-1}(M; \mu) = \lfloor M / p \rfloor - 2$ for $p \le M < p^2$ (`BuchstabFermiCovarianceAndQuotientChainBridge`).
- **What existing results left unresolved (Track A Step 2 for Uncharted Obstacle 1):**
  In `DownwardBuchstabL2TelescopeAndSawtoothCoupling`, the downward $L^2$ telescope
  $$\mathcal{E}_N(M; \mu) = 1 - \sum_{\substack{n \in [N, M-1] \\ \operatorname{Squarefree}(n+1)}} \bigl(\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu)\bigr)$$
  includes **composite squarefree steps** $n + 1$ (such as $6, 10, 14, 15, \dots$), where $n + 1$ is **not** trans-horizon rough above $n$. A classical prime-only Buchstab recurrence cannot evaluate these composite steps because $s_{n,\mu}((n + 1) j) \ne s_{n,\mu}(j)$ when $\gcd(n + 1, j) = 1$ fails or when $n + 1$ has prime factors $\le n$.
- **New content in this module (`Candidate new theorem` & `Corollary`):**
  1. **Universal First-Band Step Evaluation Without Primality (`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_first_band`, `sieveL2PrefixEnergy_moebiusReal_first_octave_closed_form`):**
     For **every** $n \ge 1$ (prime or composite!) and every $M$ in the first band $n + 1 \le M < 2(n + 1)$ ($\lfloor M / (n + 1) \rfloor = 1$), $s_{n,\mu}(n + 1) = -\mu(n + 1)$, so:
     $$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) = -\mu(n + 1)^2 \le 0.$$
     Downward telescoping from $\mathcal{E}_M(M; \mu) = 1$ gives the exact closed-form first-octave $L^2$ energy for all $1 \le N \le M \le 2N + 1$:
     $$\mathcal{E}_N(M; \mu) = 1 + \sum_{n \in \operatorname{Ico} N M} \mu(n + 1)^2.$$
  2. **Universal Second-Band $2$-Adic Parity Dichotomy Without Primality (`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_second_band_even`, `sieveL2PrefixEnergy_moebiusReal_succ_sub_of_second_band_odd`):**
     For **every** $n \ge 2$ (prime or composite!) and every $M$ in the second band $2(n + 1) \le M < 3(n + 1)$ ($\lfloor M / (n + 1) \rfloor = 2$), the second quotient term $s_{n,\mu}(2(n + 1))$ splits cleanly by the $2$-adic parity of $n + 1$:
     - **Even $n + 1$ ($2 \mid n + 1$):** By all-horizon radical divisor absorption (`sieveSeq_moebiusReal_mul_of_dvd`), $s_{n,\mu}(2(n + 1)) = s_{n,\mu}(n + 1) = -\mu(n + 1)$, yielding:
       $$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) = -2\mu(n + 1)^2 \le 0.$$
     - **Odd $n + 1$ ($\neg (2 \mid n + 1)$):** Since $2n + 1 \le 2(n + 1) \le 3n$ for all $n \ge 2$, $2$-adic valuation switching in the second octave (`sieveSeq_moebiusReal_second_octave_two_mul_odd_eq_zero`) gives $s_{n,\mu}(2(n + 1)) = 0$, yielding **exact conservation** for every odd composite or prime step:
       $$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) = 0.$$
     - **Two-Band Universal Downward Monotonicity (`sieveL2PrefixEnergy_moebiusReal_succ_le_of_lt_three_mul`):**
       Across the entire two-band trans-horizon window $M < 3(n + 1)$ ($n \ge 2$), **every** horizon step $n \to n + 1$ (prime or composite!) satisfies $\mathcal{E}_{n+1}(M; \mu) \le \mathcal{E}_n(M; \mu)$, and downward telescoping yields the exact two-band closed form (`sieveL2PrefixEnergy_moebiusReal_two_band_closed_form`).
  3. **General Composite-Step Square Completion & Dilated Energy Subadditivity (`mul_quotient_succ_step_add_dilated_eq`, `sieveL2PrefixEnergy_le_succ_add_dilated`):**
     For arbitrary $n, M \in \mathbb{N}$ (arbitrary quotient $Q = \lfloor M / (n + 1) \rfloor$) and arbitrary weight $c : \mathbb{N} \to \mathbb{R}$, completing the square over the dilated sequence $j \mapsto s_{n,c}((n + 1) j)$ proves:
     $$\mathcal{E}_n(M; c) \le \mathcal{E}_{n+1}(M; c) + \sum_{j=1}^{\lfloor M/(n+1) \rfloor} s_{n,c}((n + 1) j)^2,$$
     where the dilated energy $\sum_{j=1}^Q s_{n,c}((n + 1) j)^2$ equals the sub-sum of $\mathcal{E}_n(M; c)$ restricted to multiples of $n + 1$.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. General Single-Horizon Step & Universal First-Band Evaluation Without Primality -/

/-- Pointwise single-horizon step of `sieveBandSeq`:
`sieveBandSeq n (n + 1) c k = if n + 1 ∣ k then c (n + 1) else 0`. -/
theorem sieveBandSeq_succ_eq_ite (n : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveBandSeq n (n + 1) c k = if n + 1 ∣ k then c (n + 1) else 0 := by
  unfold sieveBandSeq sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  ring

/-- Quotient bijection for multiples of `d > 0` in `Finset.Icc 1 M`. -/
theorem sum_Icc_filter_dvd_eq_sum_Icc_div {d : ℕ} (hd : 0 < d) (M : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ (Finset.Icc 1 M).filter (fun k => d ∣ k), f k) =
      ∑ j ∈ Finset.Icc 1 (M / d), f (d * j) := by
  have hbij : (Finset.Icc 1 M).filter (fun k => d ∣ k) =
      (Finset.Icc 1 (M / d)).image (fun j => d * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hkM⟩, ⟨j, rfl⟩⟩
      have hj1 : 1 ≤ j := by
        by_contra h
        have hj0 : j = 0 := by omega
        subst hj0; omega
      exact ⟨j, ⟨hj1, (Nat.le_div_iff_mul_le hd).mpr (by linarith)⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hjM⟩, rfl⟩
      have hle := (Nat.le_div_iff_mul_le hd).mp hjM
      exact ⟨⟨Nat.mul_pos hd hj1, by linarith⟩, dvd_mul_right d j⟩
  rw [hbij, Finset.sum_image]
  intro j₁ _ j₂ _ hmul
  exact Nat.eq_of_mul_eq_mul_left hd hmul

/-- **General Single-Horizon $L^2$ Energy Step Identity (`sieveL2PrefixEnergy_succ_sub_eq`):**
For every $n, M \in \mathbb{N}$ (with $n + 1$ prime or composite) and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_{n+1}(M; c) - \mathcal{E}_n(M; c) =
  c(n + 1)^2 \left\lfloor \frac{M}{n + 1} \right\rfloor +
    2 c(n + 1) \sum_{j=1}^{\lfloor M/(n+1) \rfloor} s_{n,c}((n + 1) j).$$ -/
theorem sieveL2PrefixEnergy_succ_sub_eq (n M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c =
      c (n + 1) ^ (2 : ℕ) * ((M / (n + 1) : ℕ) : ℝ) +
        2 * c (n + 1) * ∑ j ∈ Finset.Icc 1 (M / (n + 1)), sieveSeq n c ((n + 1) * j) := by
  have hsq : (∑ k ∈ Finset.Icc 1 M, sieveBandSeq n (n + 1) c k ^ (2 : ℕ)) =
      c (n + 1) ^ (2 : ℕ) * ((M / (n + 1) : ℕ) : ℝ) := by
    have hpt : ∀ k ∈ Finset.Icc 1 M,
        sieveBandSeq n (n + 1) c k ^ (2 : ℕ) =
          if n + 1 ∣ k then c (n + 1) ^ (2 : ℕ) else 0 := by
      intro k _
      rw [sieveBandSeq_succ_eq_ite]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter,
      sum_Icc_filter_dvd_eq_sum_Icc_div (Nat.succ_pos n) M (fun _ => c (n + 1) ^ (2 : ℕ)),
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
  have hcov : (∑ k ∈ Finset.Icc 1 M, sieveSeq n c k * sieveBandSeq n (n + 1) c k) =
      c (n + 1) * ∑ j ∈ Finset.Icc 1 (M / (n + 1)), sieveSeq n c ((n + 1) * j) := by
    have hpt : ∀ k ∈ Finset.Icc 1 M,
        sieveSeq n c k * sieveBandSeq n (n + 1) c k =
          if n + 1 ∣ k then c (n + 1) * sieveSeq n c k else 0 := by
      intro k _
      rw [sieveBandSeq_succ_eq_ite]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter,
      sum_Icc_filter_dvd_eq_sum_Icc_div (Nat.succ_pos n) M (fun k => c (n + 1) * sieveSeq n c k),
      ← Finset.mul_sum]
  rw [sieveL2PrefixEnergy_horizon_band_sub n (n + 1) M c, hsq, hcov]
  ring

/-- **Sub-Horizon Zero Step (`sieveL2PrefixEnergy_succ_sub_eq_zero_of_lt`):**
Whenever $M < n + 1$, the single-horizon $L^2$ energy step across $n + 1$ vanishes identically. -/
theorem sieveL2PrefixEnergy_succ_sub_eq_zero_of_lt {n M : ℕ} (hM : M < n + 1) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c = 0 := by
  have hdiv : M / (n + 1) = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hM)
  rw [sieveL2PrefixEnergy_succ_sub_eq, hdiv]
  simp

/-- **Universal First-Band Step Formula (`sieveL2PrefixEnergy_succ_sub_of_first_band`):**
Whenever $n + 1 \le M < 2(n + 1)$ (so $\lfloor M / (n + 1) \rfloor = 1$), for **every** $n \in \mathbb{N}$
and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_{n+1}(M; c) - \mathcal{E}_n(M; c) = c(n + 1)^2 + 2 c(n + 1) s_{n,c}(n + 1).$$ -/
theorem sieveL2PrefixEnergy_succ_sub_of_first_band {n M : ℕ}
    (hM1 : n + 1 ≤ M) (hM2 : M < 2 * (n + 1)) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c =
      c (n + 1) ^ (2 : ℕ) + 2 * c (n + 1) * sieveSeq n c (n + 1) := by
  have hle : 1 ≤ M / (n + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos n)).mpr (by omega)
  have hlt : M / (n + 1) < 2 := (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr (by omega)
  have hdiv : M / (n + 1) = 1 := by omega
  rw [sieveL2PrefixEnergy_succ_sub_eq, hdiv]
  simp only [Nat.cast_one, mul_one, Finset.Icc_self, Finset.sum_singleton]

/-- **Self-Horizon Möbius Reciprocity (`sieveSeq_moebiusReal_succ_eq_neg`):**
For **every** $n \ge 1$ (prime or composite), $s_{n,\mu}(n + 1) = -\mu(n + 1)$. -/
theorem sieveSeq_moebiusReal_succ_eq_neg {n : ℕ} (hn : 1 ≤ n) :
    sieveSeq n moebiusReal (n + 1) = -moebiusReal (n + 1) :=
  sieveSeq_moebiusReal_first_octave le_rfl (by omega : n + 1 ≤ 2 * n)

/-- **Universal First-Band Möbius Step Law Without Primality
(`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_first_band`):**
For **every** $n \ge 1$ (prime or composite!) and every $M$ in the first band $n + 1 \le M < 2(n + 1)$:
$$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) = -\mu(n + 1)^2 \le 0.$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_succ_sub_of_first_band {n M : ℕ}
    (hn : 1 ≤ n) (hM1 : n + 1 ≤ M) (hM2 : M < 2 * (n + 1)) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      -moebiusReal (n + 1) ^ (2 : ℕ) := by
  rw [sieveL2PrefixEnergy_succ_sub_of_first_band hM1 hM2 moebiusReal,
    sieveSeq_moebiusReal_succ_eq_neg hn]
  ring

/-- **Exact Closed-Form First-Octave Trans-Horizon $L^2$ Energy
(`sieveL2PrefixEnergy_moebiusReal_first_octave_closed_form`):**
For every $1 \le N \le M$ with $M < 2(N + 1)$ (i.e. $M \le 2N + 1$), the downward Buchstab
$L^2$ telescope evaluates $\mathcal{E}_N(M; \mu)$ in exact closed form without any primality
restriction on intermediate integers:
$$\mathcal{E}_N(M; \mu) = 1 + \sum_{n \in \operatorname{Ico} N M} \mu(n + 1)^2.$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_first_octave_closed_form {N M : ℕ}
    (hN1 : 1 ≤ N) (hNM : N ≤ M) (hM2 : M < 2 * (N + 1)) :
    sieveL2PrefixEnergy N M moebiusReal =
      1 + ∑ n ∈ Finset.Ico N M, moebiusReal (n + 1) ^ (2 : ℕ) := by
  have hM1 : 1 ≤ M := hN1.trans hNM
  have htele := sieveL2PrefixEnergy_sub_eq_sum_Ico_succ_sub hNM M moebiusReal
  rw [sieveL2PrefixEnergy_moebiusReal_eq_one_of_le hM1 le_rfl] at htele
  have hsum : (∑ n ∈ Finset.Ico N M,
      (sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal)) =
      -∑ n ∈ Finset.Ico N M, moebiusReal (n + 1) ^ (2 : ℕ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hnN, hnM⟩ := Finset.mem_Ico.mp hn
    exact sieveL2PrefixEnergy_moebiusReal_succ_sub_of_first_band
      (hN1.trans hnN) (by omega) (by omega)
  linarith

/-! ## §2. Universal Second-Band Evaluation ($2(n + 1) \le M < 3(n + 1)$) via $2$-Adic Parity Dichotomy -/

/-- **Universal Second-Band Step Formula (`sieveL2PrefixEnergy_succ_sub_of_second_band`):**
Whenever $2(n + 1) \le M < 3(n + 1)$ (so $\lfloor M / (n + 1) \rfloor = 2$), for **every** $n \in \mathbb{N}$
and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_{n+1}(M; c) - \mathcal{E}_n(M; c) =
  2 c(n + 1)^2 + 2 c(n + 1) \bigl(s_{n,c}(n + 1) + s_{n,c}(2(n + 1))\bigr).$$ -/
theorem sieveL2PrefixEnergy_succ_sub_of_second_band {n M : ℕ}
    (hM1 : 2 * (n + 1) ≤ M) (hM2 : M < 3 * (n + 1)) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c =
      2 * c (n + 1) ^ (2 : ℕ) +
        2 * c (n + 1) * (sieveSeq n c (n + 1) + sieveSeq n c (2 * (n + 1))) := by
  have hle : 2 ≤ M / (n + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos n)).mpr (by omega)
  have hlt : M / (n + 1) < 3 := (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr (by omega)
  have hdiv : M / (n + 1) = 2 := by omega
  have hpair : Finset.Icc 1 2 = {1, 2} := by rfl
  rw [sieveL2PrefixEnergy_succ_sub_eq, hdiv, hpair,
    Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
  push_cast
  rw [mul_one, mul_comm (n + 1) 2]
  ring

/-- **Even Step Radical Evaluation (`sieveSeq_moebiusReal_two_mul_succ_of_even`):**
Whenever $2 \mid n + 1$ and $n \ge 1$, radical divisor-multiplication absorption forces
$s_{n,\mu}(2(n + 1)) = s_{n,\mu}(n + 1) = -\mu(n + 1)$. -/
theorem sieveSeq_moebiusReal_two_mul_succ_of_even {n : ℕ} (hn : 1 ≤ n) (heven : 2 ∣ n + 1) :
    sieveSeq n moebiusReal (2 * (n + 1)) = -moebiusReal (n + 1) := by
  rw [sieveSeq_moebiusReal_mul_of_dvd n heven, sieveSeq_moebiusReal_succ_eq_neg hn]

/-- **Odd Step Second-Octave Annihilation (`sieveSeq_moebiusReal_two_mul_succ_of_odd`):**
Whenever $\neg (2 \mid n + 1)$ and $n \ge 2$, $2(n + 1)$ lies in the second octave $[2n + 1, 3n]$
with $\operatorname{Coprime}(2, n + 1)$, so $s_{n,\mu}(2(n + 1)) = 0$ identically! -/
theorem sieveSeq_moebiusReal_two_mul_succ_of_odd {n : ℕ} (hn : 2 ≤ n) (hodd : ¬ 2 ∣ n + 1) :
    sieveSeq n moebiusReal (2 * (n + 1)) = 0 := by
  have hcop : Nat.Coprime 2 (n + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  exact sieveSeq_moebiusReal_second_octave_two_mul_odd_eq_zero hcop (by omega) (by omega)

/-- **Universal Second-Band Even Step Law (`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_second_band_even`):**
For **every** $n \ge 1$ with $2 \mid n + 1$ and every $M$ in the second band
$2(n + 1) \le M < 3(n + 1)$:
$$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) = -2\mu(n + 1)^2 \le 0.$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_succ_sub_of_second_band_even {n M : ℕ}
    (hn : 1 ≤ n) (heven : 2 ∣ n + 1) (hM1 : 2 * (n + 1) ≤ M) (hM2 : M < 3 * (n + 1)) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      -2 * moebiusReal (n + 1) ^ (2 : ℕ) := by
  rw [sieveL2PrefixEnergy_succ_sub_of_second_band hM1 hM2 moebiusReal,
    sieveSeq_moebiusReal_succ_eq_neg hn, sieveSeq_moebiusReal_two_mul_succ_of_even hn heven]
  ring

/-- **Universal Second-Band Odd Step Conservation Law
(`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_second_band_odd`):**
For **every** odd $n + 1$ ($\neg (2 \mid n + 1)$) with $n \ge 2$ (whether $n + 1$ is prime or
an odd composite such as $9, 15, 21, 25, \dots$) and every $M$ in the second band
$2(n + 1) \le M < 3(n + 1)$:
$$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) = 0.$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_succ_sub_of_second_band_odd {n M : ℕ}
    (hn : 2 ≤ n) (hodd : ¬ 2 ∣ n + 1) (hM1 : 2 * (n + 1) ≤ M) (hM2 : M < 3 * (n + 1)) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal = 0 := by
  rw [sieveL2PrefixEnergy_succ_sub_of_second_band hM1 hM2 moebiusReal,
    sieveSeq_moebiusReal_succ_eq_neg (by omega : 1 ≤ n),
    sieveSeq_moebiusReal_two_mul_succ_of_odd hn hodd]
  ring

/-- **Unified Two-Band Step Formula Without Primality
(`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_three_mul`):**
For **every** $n \ge 2$ (prime or composite!) and every $M < 3(n + 1)$:
$$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) =
  \begin{cases}
    0 & \text{if } M < n + 1, \\
    -\mu(n + 1)^2 & \text{if } n + 1 \le M < 2(n + 1), \\
    -2\mu(n + 1)^2 & \text{if } 2(n + 1) \le M < 3(n + 1) \text{ and } 2 \mid n + 1, \\
    0 & \text{if } 2(n + 1) \le M < 3(n + 1) \text{ and } \neg (2 \mid n + 1).
  \end{cases}$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_three_mul {n M : ℕ}
    (hn : 2 ≤ n) (hM : M < 3 * (n + 1)) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      if M < n + 1 then 0
      else if M < 2 * (n + 1) then -moebiusReal (n + 1) ^ (2 : ℕ)
      else if 2 ∣ n + 1 then -2 * moebiusReal (n + 1) ^ (2 : ℕ)
      else 0 := by
  split_ifs with h0 h1 h2
  · exact sieveL2PrefixEnergy_succ_sub_eq_zero_of_lt h0 moebiusReal
  · exact sieveL2PrefixEnergy_moebiusReal_succ_sub_of_first_band (by omega) (by omega) h1
  · exact sieveL2PrefixEnergy_moebiusReal_succ_sub_of_second_band_even (by omega) h2 (by omega) hM
  · exact sieveL2PrefixEnergy_moebiusReal_succ_sub_of_second_band_odd hn h2 (by omega) hM

/-- **Unconditional Two-Band Downward Energy Monotonicity Without Primality
(`sieveL2PrefixEnergy_moebiusReal_succ_le_of_lt_three_mul`):**
For **every** $n \ge 2$ (prime or composite!) and every $M < 3(n + 1)$:
$$\mathcal{E}_{n+1}(M; \mu) \le \mathcal{E}_n(M; \mu).$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_succ_le_of_lt_three_mul {n M : ℕ}
    (hn : 2 ≤ n) (hM : M < 3 * (n + 1)) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal ≤ sieveL2PrefixEnergy n M moebiusReal := by
  have hid := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_three_mul hn hM
  have hsq : 0 ≤ moebiusReal (n + 1) ^ (2 : ℕ) := sq_nonneg _
  split_ifs at hid <;> linarith

/-- **Exact Two-Band Closed-Form Evaluation of Trans-Horizon $L^2$ Energy
(`sieveL2PrefixEnergy_moebiusReal_two_band_closed_form`):**
For every $2 \le N \le M$ with $M < 3(N + 1)$, the downward Buchstab $L^2$ telescope evaluates
$\mathcal{E}_N(M; \mu)$ in exact closed form across both bands $[N + 1, 2N + 1]$ and
$[2N + 2, 3N + 2]$:
$$\mathcal{E}_N(M; \mu) = 1 +
  \sum_{n \in \operatorname{Ico} N M}
    \Bigl(\text{if } M < 2(n + 1) \text{ then } \mu(n + 1)^2
          \text{ else if } 2 \mid n + 1 \text{ then } 2\mu(n + 1)^2 \text{ else } 0\Bigr).$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_two_band_closed_form {N M : ℕ}
    (hN2 : 2 ≤ N) (hNM : N ≤ M) (hM3 : M < 3 * (N + 1)) :
    sieveL2PrefixEnergy N M moebiusReal =
      1 + ∑ n ∈ Finset.Ico N M,
        (if M < 2 * (n + 1) then moebiusReal (n + 1) ^ (2 : ℕ)
         else if 2 ∣ n + 1 then 2 * moebiusReal (n + 1) ^ (2 : ℕ)
         else 0) := by
  have hM1 : 1 ≤ M := by omega
  have htele := sieveL2PrefixEnergy_sub_eq_sum_Ico_succ_sub hNM M moebiusReal
  rw [sieveL2PrefixEnergy_moebiusReal_eq_one_of_le hM1 le_rfl] at htele
  have hsum : (∑ n ∈ Finset.Ico N M,
      (sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal)) =
      -∑ n ∈ Finset.Ico N M,
        (if M < 2 * (n + 1) then moebiusReal (n + 1) ^ (2 : ℕ)
         else if 2 ∣ n + 1 then 2 * moebiusReal (n + 1) ^ (2 : ℕ)
         else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hnN, hnM⟩ := Finset.mem_Ico.mp hn
    have hstep := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_three_mul
      (hN2.trans hnN) (by omega : M < 3 * (n + 1))
    rw [if_neg (by omega : ¬ M < n + 1)] at hstep
    rw [hstep]
    split_ifs <;> ring
  linarith

/-! ## §3. General Composite-Step Square Completion & Dilated Energy Subadditivity -/

/-- **Dilated Sub-Horizon $L^2$ Energy Along Multiples of $d$ (`sieveDilatedL2Energy`):**
$$\mathcal{E}_n^{\text{dil}}(d, M; c) := \sum_{j=1}^{\lfloor M / d \rfloor} s_{n,c}(d \cdot j)^2.$$ -/
def sieveDilatedL2Energy (n d M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (M / d), sieveSeq n c (d * j) ^ (2 : ℕ)

/-- **Filter-Sum Representation of `sieveDilatedL2Energy` (`sieveDilatedL2Energy_eq_sum_filter_dvd`):**
For every $d > 0$, `sieveDilatedL2Energy n d M c` is the sub-sum of `sieveL2PrefixEnergy n M c`
restricted to multiples of $d$ in $[1, M]$. -/
theorem sieveDilatedL2Energy_eq_sum_filter_dvd (n : ℕ) {d : ℕ} (hd : 0 < d)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveDilatedL2Energy n d M c =
      ∑ k ∈ (Finset.Icc 1 M).filter (fun k => d ∣ k), sieveSeq n c k ^ (2 : ℕ) := by
  unfold sieveDilatedL2Energy
  exact (sum_Icc_filter_dvd_eq_sum_Icc_div hd M (fun k => sieveSeq n c k ^ (2 : ℕ))).symm

/-- **Pointwise Domination of `sieveDilatedL2Energy` by `sieveL2PrefixEnergy`
(`sieveDilatedL2Energy_le_sieveL2PrefixEnergy`):**
For every $n, M \in \mathbb{N}$, $d > 0$, and weight $c : \mathbb{N} \to \mathbb{R}$:
$$0 \le \mathcal{E}_n^{\text{dil}}(d, M; c) \le \mathcal{E}_n(M; c).$$ -/
theorem sieveDilatedL2Energy_le_sieveL2PrefixEnergy (n : ℕ) {d : ℕ} (hd : 0 < d)
    (M : ℕ) (c : ℕ → ℝ) :
    0 ≤ sieveDilatedL2Energy n d M c ∧
      sieveDilatedL2Energy n d M c ≤ sieveL2PrefixEnergy n M c := by
  refine ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _, ?_⟩
  rw [sieveDilatedL2Energy_eq_sum_filter_dvd n hd M c]
  unfold sieveL2PrefixEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- **Finite Prefix Cauchy–Schwarz Inequality for the Dilated Sequence
(`sq_sum_Icc_dilated_sieveSeq_le_mul_sieveDilatedL2Energy`):**
For every $n, d, M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$, with
$Q = \lfloor M / d \rfloor$:
$$\Bigl(\sum_{j=1}^Q s_{n,c}(d \cdot j)\Bigr)^2 \le (Q : \mathbb{R}) \cdot \mathcal{E}_n^{\text{dil}}(d, M; c).$$ -/
theorem sq_sum_Icc_dilated_sieveSeq_le_mul_sieveDilatedL2Energy (n d M : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 (M / d), sieveSeq n c (d * j)) ^ (2 : ℕ) ≤
      ((M / d : ℕ) : ℝ) * sieveDilatedL2Energy n d M c := by
  rcases Nat.eq_zero_or_pos (M / d) with hQ0 | hQpos
  · rw [hQ0]
    simp [sieveDilatedL2Energy]
  · have hQ_pos : (0 : ℝ) < ((M / d : ℕ) : ℝ) := Nat.cast_pos.mpr hQpos
    have hnonneg : 0 ≤ ∑ j ∈ Finset.Icc 1 (M / d),
        (((M / d : ℕ) : ℝ) * sieveSeq n c (d * j) -
          ∑ i ∈ Finset.Icc 1 (M / d), sieveSeq n c (d * i)) ^ (2 : ℕ) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [sum_Icc_mul_sub_sum_sq_eq (M / d) (fun j => sieveSeq n c (d * j))] at hnonneg
    unfold sieveDilatedL2Energy
    have hpos_diff := nonneg_of_mul_nonneg_right hnonneg hQ_pos
    linarith

/-- **Universal Composite-Step Square-Completion Identity (`mul_quotient_succ_step_add_dilated_eq`):**
For **every** $n, M \in \mathbb{N}$ (prime or composite!) and weight $c : \mathbb{N} \to \mathbb{R}$,
with $Q = \lfloor M / (n + 1) \rfloor$:
$$(Q : \mathbb{R}) \cdot \Bigl(\mathcal{E}_{n+1}(M; c) - \mathcal{E}_n(M; c) + \mathcal{E}_n^{\text{dil}}(n + 1, M; c)\Bigr) =
  \Bigl(c(n + 1) \cdot (Q : \mathbb{R}) + \sum_{j=1}^Q s_{n,c}((n + 1) j)\Bigr)^2 +
    \Bigl((Q : \mathbb{R}) \cdot \mathcal{E}_n^{\text{dil}}(n + 1, M; c) -
      \Bigl(\sum_{j=1}^Q s_{n,c}((n + 1) j)\Bigr)^2\Bigr).$$ -/
theorem mul_quotient_succ_step_add_dilated_eq (n M : ℕ) (c : ℕ → ℝ) :
    ((M / (n + 1) : ℕ) : ℝ) *
        (sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c +
          sieveDilatedL2Energy n (n + 1) M c) =
      (c (n + 1) * ((M / (n + 1) : ℕ) : ℝ) +
          ∑ j ∈ Finset.Icc 1 (M / (n + 1)), sieveSeq n c ((n + 1) * j)) ^ (2 : ℕ) +
        (((M / (n + 1) : ℕ) : ℝ) * sieveDilatedL2Energy n (n + 1) M c -
          (∑ j ∈ Finset.Icc 1 (M / (n + 1)), sieveSeq n c ((n + 1) * j)) ^ (2 : ℕ)) := by
  rw [sieveL2PrefixEnergy_succ_sub_eq n M c]
  ring

/-- **Universal Composite-Step Downward $L^2$ Energy Subadditivity
(`sieveL2PrefixEnergy_le_succ_add_dilated`):**
For **every** $n, M \in \mathbb{N}$ (prime or composite!) and **every** weight $c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_n(M; c) \le \mathcal{E}_{n+1}(M; c) + \mathcal{E}_n^{\text{dil}}(n + 1, M; c).$$ -/
theorem sieveL2PrefixEnergy_le_succ_add_dilated (n M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy n M c ≤
      sieveL2PrefixEnergy (n + 1) M c + sieveDilatedL2Energy n (n + 1) M c := by
  rcases Nat.eq_zero_or_pos (M / (n + 1)) with hQ0 | hQpos
  · have hstep := sieveL2PrefixEnergy_succ_sub_eq n M c
    unfold sieveDilatedL2Energy
    rw [hQ0] at hstep ⊢
    simp at hstep ⊢
    linarith
  · have hQ_real : (0 : ℝ) < ((M / (n + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr hQpos
    have hid := mul_quotient_succ_step_add_dilated_eq n M c
    have hcs := sq_sum_Icc_dilated_sieveSeq_le_mul_sieveDilatedL2Energy n (n + 1) M c
    have hsq : 0 ≤ (c (n + 1) * ((M / (n + 1) : ℕ) : ℝ) +
        ∑ j ∈ Finset.Icc 1 (M / (n + 1)), sieveSeq n c ((n + 1) * j)) ^ (2 : ℕ) := sq_nonneg _
    have hprod_nonneg : 0 ≤ ((M / (n + 1) : ℕ) : ℝ) *
        (sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c +
          sieveDilatedL2Energy n (n + 1) M c) := by linarith
    have hnonneg := nonneg_of_mul_nonneg_right hprod_nonneg hQ_real
    linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
