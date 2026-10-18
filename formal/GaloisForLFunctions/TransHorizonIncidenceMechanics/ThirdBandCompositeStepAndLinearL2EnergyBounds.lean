import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeSquarefreeStepAndMultiOctaveL2Energy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ComplementaryQuotientAndSecondOctaveLaw

/-!
# Pillar XXVIII: Third-Band `(2, 3)`-Adic Step Classification, Three-Band Closed-Form `L²` Energy, and Linear Energy Bounds (`ThirdBandCompositeStepAndLinearL2EnergyBounds`)

## 1. Classical Baseline & Honest Classification (`README.md` §2)

- **Closest existing results:**
  - Prime-horizon quadratic-window step $\mathcal{E}_p(M; \mu) - \mathcal{E}_{p-1}(M; \mu) = \lfloor M / p \rfloor - 2 = +1$ for primes $p > 3$ in the third band $3p \le M < 4p$ (`BuchstabFermiCovarianceAndQuotientChainBridge`);
  - Complementary quotient third-band expansion `sieveSeq_third_band_eq_sum_divisors_sub` (`ComplementaryQuotientAndSecondOctaveLaw`);
  - First- and second-band composite step evaluation (`CompositeSquarefreeStepAndMultiOctaveL2Energy`).
- **What existing results left unresolved (Track A Step 3 for Uncharted Obstacle 1):**
  In the third band $3(n + 1) \le M < 4(n + 1)$ ($\lfloor M / (n + 1) \rfloor = 3$), a prime step $p = n + 1 \ge 5$ has $\mathcal{E}_p(M; \mu) - \mathcal{E}_{p-1}(M; \mu) = 3 - 2 = +1 > 0$. What happens at **composite squarefree steps** $n + 1$ in the third band (such as $n + 1 \in \{6, 10, 14, 15, 21, 22, 30, 35, \dots\}$), and how do they affect the downward Buchstab $L^2$ telescope across $M < 4(N + 1)$?
- **New content in this module (`Candidate new theorem` & `Corollary`):**
  1. **Exact Third-Band $s_{n,\mu}(3(n + 1))$ Evaluation Without Primality (`sieveSeq_moebiusReal_three_mul_succ_of_three_dvd`, `sieveSeq_moebiusReal_three_mul_succ_of_coprime_six`, `sieveSeq_moebiusReal_three_mul_succ_of_squarefree_even`):**
     For $n \ge 3$:
     - If $3 \mid n + 1$, radical divisor absorption gives $s_{n,\mu}(3(n + 1)) = -\mu(n + 1)$.
     - If $\neg(2 \mid n + 1)$ and $\neg(3 \mid n + 1)$, the complementary quotients $m = 1$ ($\mu(3(n + 1)) = -\mu(n + 1)$) and $m = 3$ ($\mu(n + 1)$) cancel identically, giving $s_{n,\mu}(3(n + 1)) = 0$.
     - If $2 \mid n + 1$, $\neg(3 \mid n + 1)$, and $\operatorname{Squarefree}(n + 1)$, the additional $m = 2$ quotient term $\mu(3(n + 1)/2) = \mu(3 \cdot (n + 1)/2) = -\mu((n + 1)/2) = \mu(n + 1)$ restores $s_{n,\mu}(3(n + 1)) = -\mu(n + 1)$!
     - Consequently, for **every** $n \ge 3$ (squarefree or not!), $\mu(n + 1) \cdot s_{n,\mu}(3(n + 1)) = -\mu(n + 1)^2$ whenever $2 \mid n + 1 \lor 3 \mid n + 1$, and $0$ whenever $\neg(2 \mid n + 1) \land \neg(3 \mid n + 1)$ (`moebiusReal_mul_sieveSeq_three_mul_succ_eq`).
  2. **Complete Third-Band $(2, 3)$-Adic Step Classification (`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_third_band`):**
     For **every** $n \ge 3$ (prime or composite!) and $3(n + 1) \le M < 4(n + 1)$:
     $$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) =
       \begin{cases}
         -3\mu(n + 1)^2 \le 0 & \text{if } 2 \mid n + 1, \\
         -\mu(n + 1)^2 \le 0 & \text{if } \neg(2 \mid n + 1) \text{ and } 3 \mid n + 1, \\
         +\mu(n + 1)^2 \ge 0 & \text{if } \neg(2 \mid n + 1) \text{ and } \neg(3 \mid n + 1).
       \end{cases}$$
     Thus every composite step divisible by $2$ or $3$ remains strictly dissipative ($\le 0$) in the third band, while $(2, 3)$-coprime steps enter the downward telescope $\mathcal{E}_N(M; \mu) = 1 - \sum (\mathcal{E}_{n+1} - \mathcal{E}_n)$ with a **negative** sign $-\mu(n + 1)^2 \le 0$!
  3. **Exact Three-Band Closed-Form $L^2$ Energy & Explicit Linear Upper Bounds (`sieveL2PrefixEnergy_moebiusReal_three_band_closed_form`, `sieveL2PrefixEnergy_moebiusReal_first_octave_le`, `sieveL2PrefixEnergy_moebiusReal_two_band_le`, `sieveL2PrefixEnergy_moebiusReal_three_band_le`):**
     Establishes the exact closed-form formula for $\mathcal{E}_N(M; \mu)$ across $3 \le N \le M < 4(N + 1)$ and proves the unconditional linear upper bounds:
     - $\mathcal{E}_N(M; \mu) \le 1 + (M - N)$ for $1 \le N \le M < 2(N + 1)$,
     - $\mathcal{E}_N(M; \mu) \le 1 + 2(M - N)$ for $2 \le N \le M < 3(N + 1)$,
     - $\mathcal{E}_N(M; \mu) \le 1 + 3(M - N)$ for $3 \le N \le M < 4(N + 1)$.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Pointwise Bounds on `moebiusReal` and Explicit Linear Bounds on the First Two Bands -/

/-- For every `k : ℕ`, `moebiusReal k ∈ {-1, 0, 1}`. -/
theorem moebiusReal_eq_or (k : ℕ) :
    moebiusReal k = -1 ∨ moebiusReal k = 0 ∨ moebiusReal k = 1 := by
  unfold moebiusReal
  rcases ArithmeticFunction.moebius_eq_or k with h | h | h <;> simp [h]

/-- For every `k : ℕ`, `0 ≤ moebiusReal k ^ 2 ≤ 1`. -/
theorem moebiusReal_sq_bounds (k : ℕ) :
    0 ≤ moebiusReal k ^ (2 : ℕ) ∧ moebiusReal k ^ (2 : ℕ) ≤ 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  rcases moebiusReal_eq_or k with h | h | h <;> { rw [h]; norm_num }

/-- If `Squarefree k`, then `moebiusReal k ^ 2 = 1`. -/
theorem moebiusReal_sq_eq_one_of_squarefree {k : ℕ} (hk : Squarefree k) :
    moebiusReal k ^ (2 : ℕ) = 1 := by
  unfold moebiusReal
  have h := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hk
  rcases ArithmeticFunction.moebius_eq_or k with h0 | h1 | h2
  · exact absurd h0 h
  · simp [h1]
  · simp [h2]

/-- **Explicit Linear Upper Bound on First-Octave Trans-Horizon $L^2$ Energy
(`sieveL2PrefixEnergy_moebiusReal_first_octave_le`):**
For every $1 \le N \le M$ with $M < 2(N + 1)$:
$$\mathcal{E}_N(M; \mu) \le 1 + (M - N : \mathbb{R}).$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_first_octave_le {N M : ℕ}
    (hN1 : 1 ≤ N) (hNM : N ≤ M) (hM2 : M < 2 * (N + 1)) :
    sieveL2PrefixEnergy N M moebiusReal ≤ 1 + ((M - N : ℕ) : ℝ) := by
  rw [sieveL2PrefixEnergy_moebiusReal_first_octave_closed_form hN1 hNM hM2]
  have hsum : (∑ n ∈ Finset.Ico N M, moebiusReal (n + 1) ^ (2 : ℕ)) ≤
      ∑ _n ∈ Finset.Ico N M, (1 : ℝ) :=
    Finset.sum_le_sum fun n _ => (moebiusReal_sq_bounds (n + 1)).2
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one] at hsum
  linarith

/-- **Explicit Linear Upper Bound on Two-Band Trans-Horizon $L^2$ Energy
(`sieveL2PrefixEnergy_moebiusReal_two_band_le`):**
For every $2 \le N \le M$ with $M < 3(N + 1)$:
$$\mathcal{E}_N(M; \mu) \le 1 + 2(M - N : \mathbb{R}).$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_two_band_le {N M : ℕ}
    (hN2 : 2 ≤ N) (hNM : N ≤ M) (hM3 : M < 3 * (N + 1)) :
    sieveL2PrefixEnergy N M moebiusReal ≤ 1 + 2 * ((M - N : ℕ) : ℝ) := by
  rw [sieveL2PrefixEnergy_moebiusReal_two_band_closed_form hN2 hNM hM3]
  have hsum : (∑ n ∈ Finset.Ico N M,
      (if M < 2 * (n + 1) then moebiusReal (n + 1) ^ (2 : ℕ)
       else if 2 ∣ n + 1 then 2 * moebiusReal (n + 1) ^ (2 : ℕ)
       else 0)) ≤ ∑ _n ∈ Finset.Ico N M, (2 : ℝ) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have h0 := (moebiusReal_sq_bounds (n + 1)).1
    have h1 := (moebiusReal_sq_bounds (n + 1)).2
    split_ifs <;> linarith
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  linarith

/-! ## §2. Third-Band Evaluation of $s_{n,\mu}(3(n + 1))$ via $(2, 3)$-Adic Dichotomy -/

/-- **Universal Third-Band Step Formula (`sieveL2PrefixEnergy_succ_sub_of_third_band`):**
Whenever $3(n + 1) \le M < 4(n + 1)$ (so $\lfloor M / (n + 1) \rfloor = 3$), for **every** $n \in \mathbb{N}$
and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_{n+1}(M; c) - \mathcal{E}_n(M; c) =
  3 c(n + 1)^2 + 2 c(n + 1) \bigl(s_{n,c}(n + 1) + s_{n,c}(2(n + 1)) + s_{n,c}(3(n + 1))\bigr).$$ -/
theorem sieveL2PrefixEnergy_succ_sub_of_third_band {n M : ℕ}
    (hM1 : 3 * (n + 1) ≤ M) (hM2 : M < 4 * (n + 1)) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c =
      3 * c (n + 1) ^ (2 : ℕ) +
        2 * c (n + 1) *
          (sieveSeq n c (n + 1) + sieveSeq n c (2 * (n + 1)) + sieveSeq n c (3 * (n + 1))) := by
  have hle : 3 ≤ M / (n + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos n)).mpr (by omega)
  have hlt : M / (n + 1) < 4 := (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr (by omega)
  have hdiv : M / (n + 1) = 3 := by omega
  rw [sieveL2PrefixEnergy_succ_sub_eq, hdiv, Icc_one_three_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff,
    or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  push_cast
  rw [mul_one, mul_comm (n + 1) 2, mul_comm (n + 1) 3]
  ring

/-- **$3$-Divisible Radical Evaluation (`sieveSeq_moebiusReal_three_mul_succ_of_three_dvd`):**
Whenever $3 \mid n + 1$ and $n \ge 1$, radical divisor-multiplication absorption forces
$s_{n,\mu}(3(n + 1)) = s_{n,\mu}(n + 1) = -\mu(n + 1)$. -/
theorem sieveSeq_moebiusReal_three_mul_succ_of_three_dvd {n : ℕ}
    (hn : 1 ≤ n) (h3 : 3 ∣ n + 1) :
    sieveSeq n moebiusReal (3 * (n + 1)) = -moebiusReal (n + 1) := by
  rw [sieveSeq_moebiusReal_mul_of_dvd n h3, sieveSeq_moebiusReal_succ_eq_neg hn]

/-- **$(2, 3)$-Coprime Third-Band Annihilation (`sieveSeq_moebiusReal_three_mul_succ_of_coprime_six`):**
Whenever $n \ge 3$, $\neg(2 \mid n + 1)$, and $\neg(3 \mid n + 1)$, $3(n + 1)$ lies in the third
band $[3n + 1, 4n]$ and $s_{n,\mu}(3(n + 1)) = 0$ identically! -/
theorem sieveSeq_moebiusReal_three_mul_succ_of_coprime_six {n : ℕ}
    (hn : 3 ≤ n) (h2 : ¬ 2 ∣ n + 1) (h3 : ¬ 3 ∣ n + 1) :
    sieveSeq n moebiusReal (3 * (n + 1)) = 0 := by
  have hk1 : 3 * n + 1 ≤ 3 * (n + 1) := by omega
  have hk2 : 3 * (n + 1) ≤ 4 * n := by omega
  have hsum0 : (∑ d ∈ (3 * (n + 1)).divisors, moebiusReal d) = 0 :=
    sum_divisors_moebiusReal_eq_zero (by omega : 2 ≤ 3 * (n + 1))
  have hnot2 : ¬ 2 ∣ 3 * (n + 1) := by
    intro hdvd
    have hcop23 : Nat.Coprime 2 3 := by decide
    exact h2 (hcop23.dvd_of_dvd_mul_left hdvd)
  have hdvd3 : 3 ∣ 3 * (n + 1) := dvd_mul_right 3 (n + 1)
  have hdiv3 : 3 * (n + 1) / 3 = n + 1 := Nat.mul_div_cancel_left (n + 1) (by decide : 0 < 3)
  have hcop3 : Nat.Coprime 3 (n + 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hmu3 : moebiusReal (3 * (n + 1)) = -moebiusReal (n + 1) := by
    unfold moebiusReal
    rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hcop3,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    push_cast
    ring
  rw [sieveSeq_third_band_eq_sum_divisors_sub hk1 hk2 moebiusReal,
    hsum0, if_neg hnot2, if_pos hdvd3, hdiv3, hmu3]
  ring

/-- **Even Squarefree Third-Band Evaluation (`sieveSeq_moebiusReal_three_mul_succ_of_squarefree_even`):**
Whenever $n \ge 3$, $\operatorname{Squarefree}(n + 1)$, and $2 \mid n + 1$ (whether $3 \mid n + 1$
or $\neg(3 \mid n + 1)$!), $s_{n,\mu}(3(n + 1)) = -\mu(n + 1)$. -/
theorem sieveSeq_moebiusReal_three_mul_succ_of_squarefree_even {n : ℕ}
    (hn : 3 ≤ n) (hsq : Squarefree (n + 1)) (h2 : 2 ∣ n + 1) :
    sieveSeq n moebiusReal (3 * (n + 1)) = -moebiusReal (n + 1) := by
  by_cases h3 : 3 ∣ n + 1
  · exact sieveSeq_moebiusReal_three_mul_succ_of_three_dvd (by omega) h3
  · have hk1 : 3 * n + 1 ≤ 3 * (n + 1) := by omega
    have hk2 : 3 * (n + 1) ≤ 4 * n := by omega
    have hsum0 : (∑ d ∈ (3 * (n + 1)).divisors, moebiusReal d) = 0 :=
      sum_divisors_moebiusReal_eq_zero (by omega : 2 ≤ 3 * (n + 1))
    obtain ⟨u, hu⟩ := h2
    have hsq_2u : Squarefree (2 * u) := hu ▸ hsq
    have hcop2u : Nat.Coprime 2 u := Nat.coprime_of_squarefree_mul hsq_2u
    have hnot3u : ¬ 3 ∣ u := fun h3u => h3 (hu ▸ dvd_mul_of_dvd_right h3u 2)
    have hcop3u : Nat.Coprime 3 u := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot3u
    have hcop3_n1 : Nat.Coprime 3 (n + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hdvd2 : 2 ∣ 3 * (n + 1) := ⟨3 * u, by linarith⟩
    have hdvd3 : 3 ∣ 3 * (n + 1) := dvd_mul_right 3 (n + 1)
    have hdiv2 : 3 * (n + 1) / 2 = 3 * u := by
      have : 3 * (n + 1) = 2 * (3 * u) := by linarith
      rw [this, Nat.mul_div_cancel_left (3 * u) (by decide : 0 < 2)]
    have hdiv3 : 3 * (n + 1) / 3 = n + 1 := Nat.mul_div_cancel_left (n + 1) (by decide : 0 < 3)
    have hmu_3n1 : moebiusReal (3 * (n + 1)) = -moebiusReal (n + 1) := by
      unfold moebiusReal
      rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius hcop3_n1,
        ArithmeticFunction.moebius_apply_prime Nat.prime_three]
      push_cast; ring
    have hmu_n1 : moebiusReal (n + 1) = -moebiusReal u := by
      rw [hu]
      unfold moebiusReal
      rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius hcop2u,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      push_cast; ring
    have hmu_3u : moebiusReal (3 * u) = -moebiusReal u := by
      unfold moebiusReal
      rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_moebius hcop3u,
        ArithmeticFunction.moebius_apply_prime Nat.prime_three]
      push_cast; ring
    rw [sieveSeq_third_band_eq_sum_divisors_sub hk1 hk2 moebiusReal,
      hsum0, if_pos hdvd2, if_pos hdvd3, hdiv2, hdiv3, hmu_3n1, hmu_3u, hmu_n1]
    ring

/-- **Universal Weighted Third-Multiple Product Law (`moebiusReal_mul_sieveSeq_three_mul_succ_eq`):**
For **every** $n \ge 3$ (without any squarefreeness or primality assumption on $n + 1$):
$$\mu(n + 1) \cdot s_{n,\mu}(3(n + 1)) =
  \begin{cases}
    -\mu(n + 1)^2 & \text{if } 2 \mid n + 1 \text{ or } 3 \mid n + 1, \\
    0 & \text{if } \neg(2 \mid n + 1) \text{ and } \neg(3 \mid n + 1).
  \end{cases}$$ -/
theorem moebiusReal_mul_sieveSeq_three_mul_succ_eq {n : ℕ} (hn : 3 ≤ n) :
    moebiusReal (n + 1) * sieveSeq n moebiusReal (3 * (n + 1)) =
      if 2 ∣ n + 1 ∨ 3 ∣ n + 1 then -moebiusReal (n + 1) ^ (2 : ℕ) else 0 := by
  by_cases hsq : Squarefree (n + 1)
  · by_cases h2 : 2 ∣ n + 1
    · rw [if_pos (Or.inl h2), sieveSeq_moebiusReal_three_mul_succ_of_squarefree_even hn hsq h2]
      ring
    · by_cases h3 : 3 ∣ n + 1
      · rw [if_pos (Or.inr h3), sieveSeq_moebiusReal_three_mul_succ_of_three_dvd (by omega) h3]
        ring
      · have hnot : ¬ (2 ∣ n + 1 ∨ 3 ∣ n + 1) := by tauto
        rw [if_neg hnot, sieveSeq_moebiusReal_three_mul_succ_of_coprime_six hn h2 h3, mul_zero]
  · rw [moebiusReal_eq_zero_of_not_squarefree (n + 1) hsq]
    split_ifs <;> ring

/-! ## §3. Complete Third-Band Step Classification & Three-Band Closed-Form `L²` Energy -/

/-- **Complete Third-Band $(2, 3)$-Adic Step Classification Without Primality
(`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_third_band`):**
For **every** $n \ge 3$ (prime or composite!) and every $M$ in the third band
$3(n + 1) \le M < 4(n + 1)$:
$$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) =
  \begin{cases}
    -3\mu(n + 1)^2 & \text{if } 2 \mid n + 1, \\
    -\mu(n + 1)^2 & \text{if } \neg(2 \mid n + 1) \text{ and } 3 \mid n + 1, \\
    +\mu(n + 1)^2 & \text{if } \neg(2 \mid n + 1) \text{ and } \neg(3 \mid n + 1).
  \end{cases}$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_succ_sub_of_third_band {n M : ℕ}
    (hn : 3 ≤ n) (hM1 : 3 * (n + 1) ≤ M) (hM2 : M < 4 * (n + 1)) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      if 2 ∣ n + 1 then -3 * moebiusReal (n + 1) ^ (2 : ℕ)
      else if 3 ∣ n + 1 then -moebiusReal (n + 1) ^ (2 : ℕ)
      else moebiusReal (n + 1) ^ (2 : ℕ) := by
  rw [sieveL2PrefixEnergy_succ_sub_of_third_band hM1 hM2 moebiusReal,
    sieveSeq_moebiusReal_succ_eq_neg (by omega : 1 ≤ n)]
  have h3prod := moebiusReal_mul_sieveSeq_three_mul_succ_eq hn
  by_cases h2 : 2 ∣ n + 1
  · rw [if_pos h2, sieveSeq_moebiusReal_two_mul_succ_of_even (by omega) h2]
    rw [if_pos (Or.inl h2)] at h3prod
    linear_combination 2 * h3prod
  · rw [if_neg h2, sieveSeq_moebiusReal_two_mul_succ_of_odd (by omega) h2]
    by_cases h3 : 3 ∣ n + 1
    · rw [if_pos h3]
      rw [if_pos (Or.inr h3)] at h3prod
      linear_combination 2 * h3prod
    · rw [if_neg h3]
      have hnot : ¬ (2 ∣ n + 1 ∨ 3 ∣ n + 1) := by tauto
      rw [if_neg hnot] at h3prod
      linear_combination 2 * h3prod

/-- **Unified Three-Band Step Formula Without Primality
(`sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_four_mul`):**
For **every** $n \ge 3$ (prime or composite!) and every $M < 4(n + 1)$:
$$\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu) =
  \begin{cases}
    0 & \text{if } M < n + 1, \\
    -\mu(n + 1)^2 & \text{if } n + 1 \le M < 2(n + 1), \\
    -2\mu(n + 1)^2 & \text{if } 2(n + 1) \le M < 3(n + 1) \text{ and } 2 \mid n + 1, \\
    0 & \text{if } 2(n + 1) \le M < 3(n + 1) \text{ and } \neg(2 \mid n + 1), \\
    -3\mu(n + 1)^2 & \text{if } 3(n + 1) \le M < 4(n + 1) \text{ and } 2 \mid n + 1, \\
    -\mu(n + 1)^2 & \text{if } 3(n + 1) \le M < 4(n + 1) \text{ and } \neg(2 \mid n + 1) \text{ and } 3 \mid n + 1, \\
    +\mu(n + 1)^2 & \text{if } 3(n + 1) \le M < 4(n + 1) \text{ and } \neg(2 \mid n + 1) \text{ and } \neg(3 \mid n + 1).
  \end{cases}$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_four_mul {n M : ℕ}
    (hn : 3 ≤ n) (hM : M < 4 * (n + 1)) :
    sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
      if M < n + 1 then 0
      else if M < 2 * (n + 1) then -moebiusReal (n + 1) ^ (2 : ℕ)
      else if M < 3 * (n + 1) then
        (if 2 ∣ n + 1 then -2 * moebiusReal (n + 1) ^ (2 : ℕ) else 0)
      else
        (if 2 ∣ n + 1 then -3 * moebiusReal (n + 1) ^ (2 : ℕ)
         else if 3 ∣ n + 1 then -moebiusReal (n + 1) ^ (2 : ℕ)
         else moebiusReal (n + 1) ^ (2 : ℕ)) := by
  by_cases h0 : M < n + 1
  · rw [if_pos h0]
    exact sieveL2PrefixEnergy_succ_sub_eq_zero_of_lt h0 moebiusReal
  · rw [if_neg h0]
    by_cases h1 : M < 2 * (n + 1)
    · rw [if_pos h1]
      exact sieveL2PrefixEnergy_moebiusReal_succ_sub_of_first_band (by omega) (by omega) h1
    · rw [if_neg h1]
      by_cases h2 : M < 3 * (n + 1)
      · rw [if_pos h2]
        have h := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_three_mul (by omega : 2 ≤ n) h2
        rw [if_neg h0, if_neg h1] at h
        exact h
      · rw [if_neg h2]
        exact sieveL2PrefixEnergy_moebiusReal_succ_sub_of_third_band hn (by omega) hM

/-- **Exact Three-Band Closed-Form Evaluation of Trans-Horizon $L^2$ Energy
(`sieveL2PrefixEnergy_moebiusReal_three_band_closed_form`):**
For every $3 \le N \le M$ with $M < 4(N + 1)$, the downward Buchstab $L^2$ telescope evaluates
$\mathcal{E}_N(M; \mu)$ in exact closed form across all three trans-horizon bands:
$$\mathcal{E}_N(M; \mu) = 1 +
  \sum_{n \in \operatorname{Ico} N M}
    \begin{cases}
      \mu(n + 1)^2 & \text{if } M < 2(n + 1), \\
      2\mu(n + 1)^2 & \text{if } 2(n + 1) \le M < 3(n + 1) \text{ and } 2 \mid n + 1, \\
      0 & \text{if } 2(n + 1) \le M < 3(n + 1) \text{ and } \neg(2 \mid n + 1), \\
      3\mu(n + 1)^2 & \text{if } 3(n + 1) \le M \text{ and } 2 \mid n + 1, \\
      \mu(n + 1)^2 & \text{if } 3(n + 1) \le M \text{ and } \neg(2 \mid n + 1) \text{ and } 3 \mid n + 1, \\
      -\mu(n + 1)^2 & \text{if } 3(n + 1) \le M \text{ and } \neg(2 \mid n + 1) \text{ and } \neg(3 \mid n + 1).
    \end{cases}$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_three_band_closed_form {N M : ℕ}
    (hN3 : 3 ≤ N) (hNM : N ≤ M) (hM4 : M < 4 * (N + 1)) :
    sieveL2PrefixEnergy N M moebiusReal =
      1 + ∑ n ∈ Finset.Ico N M,
        (if M < 2 * (n + 1) then moebiusReal (n + 1) ^ (2 : ℕ)
         else if M < 3 * (n + 1) then
           (if 2 ∣ n + 1 then 2 * moebiusReal (n + 1) ^ (2 : ℕ) else 0)
         else
           (if 2 ∣ n + 1 then 3 * moebiusReal (n + 1) ^ (2 : ℕ)
            else if 3 ∣ n + 1 then moebiusReal (n + 1) ^ (2 : ℕ)
            else -moebiusReal (n + 1) ^ (2 : ℕ))) := by
  have hM1 : 1 ≤ M := by omega
  have htele := sieveL2PrefixEnergy_sub_eq_sum_Ico_succ_sub hNM M moebiusReal
  rw [sieveL2PrefixEnergy_moebiusReal_eq_one_of_le hM1 le_rfl] at htele
  have hsum : (∑ n ∈ Finset.Ico N M,
      (sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal)) =
      -∑ n ∈ Finset.Ico N M,
        (if M < 2 * (n + 1) then moebiusReal (n + 1) ^ (2 : ℕ)
         else if M < 3 * (n + 1) then
           (if 2 ∣ n + 1 then 2 * moebiusReal (n + 1) ^ (2 : ℕ) else 0)
         else
           (if 2 ∣ n + 1 then 3 * moebiusReal (n + 1) ^ (2 : ℕ)
            else if 3 ∣ n + 1 then moebiusReal (n + 1) ^ (2 : ℕ)
            else -moebiusReal (n + 1) ^ (2 : ℕ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hnN, hnM⟩ := Finset.mem_Ico.mp hn
    have hstep := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_four_mul
      (hN3.trans hnN) (by omega : M < 4 * (n + 1))
    rw [if_neg (by omega : ¬ M < n + 1)] at hstep
    rw [hstep]
    split_ifs <;> ring
  linarith

/-- **Explicit Linear Upper Bound on Three-Band Trans-Horizon $L^2$ Energy
(`sieveL2PrefixEnergy_moebiusReal_three_band_le`):**
For every $3 \le N \le M$ with $M < 4(N + 1)$:
$$\mathcal{E}_N(M; \mu) \le 1 + 3(M - N : \mathbb{R}).$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_three_band_le {N M : ℕ}
    (hN3 : 3 ≤ N) (hNM : N ≤ M) (hM4 : M < 4 * (N + 1)) :
    sieveL2PrefixEnergy N M moebiusReal ≤ 1 + 3 * ((M - N : ℕ) : ℝ) := by
  rw [sieveL2PrefixEnergy_moebiusReal_three_band_closed_form hN3 hNM hM4]
  have hsum : (∑ n ∈ Finset.Ico N M,
      (if M < 2 * (n + 1) then moebiusReal (n + 1) ^ (2 : ℕ)
       else if M < 3 * (n + 1) then
         (if 2 ∣ n + 1 then 2 * moebiusReal (n + 1) ^ (2 : ℕ) else 0)
       else
         (if 2 ∣ n + 1 then 3 * moebiusReal (n + 1) ^ (2 : ℕ)
          else if 3 ∣ n + 1 then moebiusReal (n + 1) ^ (2 : ℕ)
          else -moebiusReal (n + 1) ^ (2 : ℕ)))) ≤
      ∑ _n ∈ Finset.Ico N M, (3 : ℝ) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have h0 := (moebiusReal_sq_bounds (n + 1)).1
    have h1 := (moebiusReal_sq_bounds (n + 1)).2
    split_ifs <;> linarith
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
