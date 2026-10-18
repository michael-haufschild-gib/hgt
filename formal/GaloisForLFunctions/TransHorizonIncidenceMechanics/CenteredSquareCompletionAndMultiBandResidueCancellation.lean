import GaloisForLFunctions.TransHorizonIncidenceMechanics.OddEigenvectorNodalModulusBalanceAndFourthBandStepLaw

/-!
# Centered Square Completion, Half-Band Cancellation Criterion, and Consecutive Parity-Pair $L^2$ Slope Reduction

This module advances **Step 3 (Sub-route 3C)** of the CHMD closure programme
(`docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md`) for trans-horizon $L^2$ prefix
energy $\mathcal{E}_N(M; \mu)$ across multi-band and arbitrary-ratio regimes $M / N$:

1. **Universal Centered Square-Completion Identity (`mul_sub_two_sieveL2PrefixEnergy_moebiusReal_sub_succ_eq_sq_sub_sq`)**:
   - Starting from the centered $(B - 2)$ step law (`sieveL2PrefixEnergy_moebiusReal_succ_sub_eq_centered`)
     with $B = \lfloor M / (n + 1) \rfloor \ge 1$ and $S_2 = \sum_{q \in \operatorname{Icc} 2 B} s_{n,\mu}(q(n + 1))$,
     multiplying by $(B - 2)$ and completing the square against the ground term $(B - 2)\mu(n + 1)^2$
     yields the exact identity
     $$(B - 2)\bigl(\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu)\bigr)
       = S_2^2 - \Bigl((B - 2)\mu(n + 1) + S_2\Bigr)^2.$$
   - For every band $B \ge 3$ ($M \ge 3(n + 1)$), dropping the non-negative square
     $\bigl((B - 2)\mu(n + 1) + S_2\bigr)^2 \ge 0$ completely absorbs the $q = 1$ ground term
     $\mu(n + 1)^2$ and proves
     $$\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu)
       \le \frac{1}{B - 2}\Bigl(\sum_{q \in \operatorname{Icc} 2 B} s_{n,\mu}(q(n + 1))\Bigr)^2$$
     (`sieveL2PrefixEnergy_moebiusReal_sub_succ_le_div_sub_two_sq`).

2. **Half-Band Cancellation Criterion for Downward $L^2$ Dissipation (`sieveL2PrefixEnergy_moebiusReal_sub_succ_nonpos_of_abs_sum_le_half`)**:
   - Whenever $B = \lfloor M / (n + 1) \rfloor \ge 2$ and the higher-quotient sum $S_2$ satisfies
     $|S_2| \le (B - 2) / 2$, the downward Buchstab step is unconditionally dissipative:
     $$\mathcal{E}_n(M; \mu) \le \mathcal{E}_{n+1}(M; \mu).$$
   - Thus, at arbitrarily large trans-horizon ratios $B = \lfloor M / (n + 1) \rfloor \ge 3$,
     cancellation of $S_2$ below half the trivial count $(B - 2) / 2$ suffices to make the
     downward $L^2$ step non-increasing.

3. **Consecutive Two-Step Parity-Pair Slope Reduction (`sieveL2PrefixEnergy_moebiusReal_sub_add_two_second_band_le_two`, `sieveL2PrefixEnergy_moebiusReal_sub_add_two_third_band_le_four`)**:
   - Pairing consecutive horizon steps $n \to n + 1 \to n + 2$:
     - In the second band $2(n + 2) \le M < 3(n + 1)$ ($n \ge 2$), exact parity alternation
       combines the even step ($\le 2$) with the odd conservation step ($= 0$) to give
       $\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+2}(M; \mu) \le 2$ (average slope $\le 1$ per step).
     - In the third band $3(n + 2) \le M < 4(n + 1)$ ($n \ge 3$), exact parity alternation
       combines the even step ($\le 3$) with the odd step ($\le 1$) to give
       $\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+2}(M; \mu) \le 4$ (average slope $\le 2$ per step),
       and when the odd step is squarefree and coprime to $3$ (e.g. any prime $p \ge 5$), its $-1$
       downward contribution actively cancels part of the even step to give
       $\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+2}(M; \mu) \le 2$ (average slope $\le 1$ per step).
-/

open Finset
open RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Universal Centered Square-Completion Identity & Ground-Term Absorption -/

/-- Higher-quotient sum $S_2(n, M) = \sum_{q \in \operatorname{Icc} 2 \lfloor M / (n + 1) \rfloor} s_{n,\mu}(q(n + 1))$
appearing in the centered Buchstab $L^2$ step identity. -/
def higherQuotientSieveSum (n M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 (M / (n + 1)), sieveSeq n moebiusReal (q * (n + 1))

/-- **Universal Centered Square-Completion Identity
(`mul_sub_two_sieveL2PrefixEnergy_moebiusReal_sub_succ_eq_sq_sub_sq`):**
For every $n \ge 1$ and $M \ge n + 1$, with $B = \lfloor M / (n + 1) \rfloor$ and
$S_2 = \operatorname{higherQuotientSieveSum}(n, M)$, whenever $\operatorname{Squarefree}(n + 1)$
(so $\mu(n + 1)^2 = 1$):
$$(B - 2)\bigl(\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu)\bigr)
  = S_2^2 - \bigl((B - 2)\mu(n + 1) + S_2\bigr)^2.$$
More generally, without assuming `Squarefree (n + 1)`, multiplying $S_2$ by $\mu(n + 1)$ gives:
$$(B - 2)\bigl(\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu)\bigr)
  = \bigl(\mu(n + 1) S_2\bigr)^2 - \bigl((B - 2)\mu(n + 1)^2 + \mu(n + 1) S_2\bigr)^2.$$
(Classification: Candidate new theorem.) -/
theorem mul_sub_two_sieveL2PrefixEnergy_moebiusReal_sub_succ_eq_sq_sub_sq {n M : ℕ}
    (hn : 1 ≤ n) (hlo : n + 1 ≤ M) :
    (((M / (n + 1) : ℕ) : ℝ) - 2) *
        (sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 1) M moebiusReal) =
      (moebiusReal (n + 1) * higherQuotientSieveSum n M) ^ (2 : ℕ) -
        ((((M / (n + 1) : ℕ) : ℝ) - 2) * moebiusReal (n + 1) ^ (2 : ℕ) +
          moebiusReal (n + 1) * higherQuotientSieveSum n M) ^ (2 : ℕ) := by
  have hstep := sieveL2PrefixEnergy_moebiusReal_succ_sub_eq_centered hn hlo
  change sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
    (((M / (n + 1) : ℕ) : ℝ) - 2) * moebiusReal (n + 1) ^ (2 : ℕ) +
      2 * moebiusReal (n + 1) * higherQuotientSieveSum n M at hstep
  rcases moebiusReal_eq_or (n + 1) with h | h | h <;> {
    rw [h] at hstep ⊢
    linear_combination -((((M / (n + 1) : ℕ) : ℝ) - 2) * hstep)
  }

/-- **Ground-Term-Free Upper Bound on $(B - 2)(\mathcal{E}_n - \mathcal{E}_{n+1})$
(`mul_sub_two_sieveL2PrefixEnergy_moebiusReal_sub_succ_le_sq`):**
For every $n \ge 1$ and $M \ge n + 1$, with $B = \lfloor M / (n + 1) \rfloor$:
$$(B - 2)\bigl(\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu)\bigr)
  \le \bigl(\mu(n + 1) \operatorname{higherQuotientSieveSum}(n, M)\bigr)^2
  \le \operatorname{higherQuotientSieveSum}(n, M)^2.$$
(Classification: Corollary.) -/
theorem mul_sub_two_sieveL2PrefixEnergy_moebiusReal_sub_succ_le_sq {n M : ℕ}
    (hn : 1 ≤ n) (hlo : n + 1 ≤ M) :
    (((M / (n + 1) : ℕ) : ℝ) - 2) *
        (sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 1) M moebiusReal) ≤
      higherQuotientSieveSum n M ^ (2 : ℕ) := by
  have hid := mul_sub_two_sieveL2PrefixEnergy_moebiusReal_sub_succ_eq_sq_sub_sq hn hlo
  have hsq_nonneg : 0 ≤ ((((M / (n + 1) : ℕ) : ℝ) - 2) * moebiusReal (n + 1) ^ (2 : ℕ) +
      moebiusReal (n + 1) * higherQuotientSieveSum n M) ^ (2 : ℕ) := sq_nonneg _
  have hmu_le : (moebiusReal (n + 1) * higherQuotientSieveSum n M) ^ (2 : ℕ) ≤
      higherQuotientSieveSum n M ^ (2 : ℕ) := by
    rw [mul_pow]
    have h1 := (moebiusReal_sq_bounds (n + 1)).2
    have h2 : 0 ≤ higherQuotientSieveSum n M ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  linarith

/-- **High-Band ($B \ge 3$) Downward Step Bound Without Ground Penalty
(`sieveL2PrefixEnergy_moebiusReal_sub_succ_le_div_sub_two_sq`):**
For every $n \ge 1$ and $M \ge 3(n + 1)$ (so $B = \lfloor M / (n + 1) \rfloor \ge 3$ and $B - 2 \ge 1$):
$$\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+1}(M; \mu)
  \le \frac{1}{B - 2}\Bigl(\sum_{q \in \operatorname{Icc} 2 B} s_{n,\mu}(q(n + 1))\Bigr)^2.$$
(Classification: Candidate new theorem.) -/
theorem sieveL2PrefixEnergy_moebiusReal_sub_succ_le_div_sub_two_sq {n M : ℕ}
    (hn : 1 ≤ n) (hM : 3 * (n + 1) ≤ M) :
    sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 1) M moebiusReal ≤
      higherQuotientSieveSum n M ^ (2 : ℕ) / (((M / (n + 1) : ℕ) : ℝ) - 2) := by
  have hB3 : 3 ≤ M / (n + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hB3_real : (3 : ℝ) ≤ ((M / (n + 1) : ℕ) : ℝ) := by exact_mod_cast hB3
  have hpos : (0 : ℝ) < ((M / (n + 1) : ℕ) : ℝ) - 2 := by linarith
  rw [le_div_iff₀ hpos, mul_comm]
  exact mul_sub_two_sieveL2PrefixEnergy_moebiusReal_sub_succ_le_sq hn (by omega)

/-! ## §2. Half-Band Cancellation Criterion for Downward $L^2$ Dissipation -/

/-- **Half-Band Cancellation Criterion for Downward $L^2$ Dissipation
(`sieveL2PrefixEnergy_moebiusReal_sub_succ_nonpos_of_abs_sum_le_half`):**
For every $n \ge 1$ and $M \ge 2(n + 1)$ ($B = \lfloor M / (n + 1) \rfloor \ge 2$), if the
higher-quotient sum satisfies
$$|\operatorname{higherQuotientSieveSum}(n, M)| \le \frac{B - 2}{2},$$
then the downward Buchstab step is non-positive:
$$\mathcal{E}_n(M; \mu) \le \mathcal{E}_{n+1}(M; \mu).$$
(Classification: Candidate new theorem.) -/
theorem sieveL2PrefixEnergy_moebiusReal_sub_succ_nonpos_of_abs_sum_le_half {n M : ℕ}
    (hn : 1 ≤ n) (hM : 2 * (n + 1) ≤ M)
    (hcancel : |higherQuotientSieveSum n M| ≤ (((M / (n + 1) : ℕ) : ℝ) - 2) / 2) :
    sieveL2PrefixEnergy n M moebiusReal ≤ sieveL2PrefixEnergy (n + 1) M moebiusReal := by
  have hlo : n + 1 ≤ M := by omega
  have hstep := sieveL2PrefixEnergy_moebiusReal_succ_sub_eq_centered hn hlo
  change sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal =
    (((M / (n + 1) : ℕ) : ℝ) - 2) * moebiusReal (n + 1) ^ (2 : ℕ) +
      2 * moebiusReal (n + 1) * higherQuotientSieveSum n M at hstep
  rcases moebiusReal_eq_or (n + 1) with h | h | h
  · rw [h] at hstep
    have h1 : -|higherQuotientSieveSum n M| ≤ higherQuotientSieveSum n M := neg_abs_le _
    have h2 : higherQuotientSieveSum n M ≤ |higherQuotientSieveSum n M| := le_abs_self _
    linarith
  · rw [h] at hstep
    linarith
  · rw [h] at hstep
    have h1 : -|higherQuotientSieveSum n M| ≤ higherQuotientSieveSum n M := neg_abs_le _
    linarith

/-! ## §3. Consecutive Two-Step Parity-Pair Slope Reduction in the Second & Third Bands -/

/-- Exact two-step downward identity:
`(E n - E (n + 2)) = (E n - E (n + 1)) + (E (n + 1) - E (n + 2))`. -/
theorem sieveL2PrefixEnergy_sub_add_two_eq (n M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy n M c - sieveL2PrefixEnergy (n + 2) M c =
      (sieveL2PrefixEnergy n M c - sieveL2PrefixEnergy (n + 1) M c) +
        (sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy (n + 2) M c) := by
  ring

/-- **Second-Band Consecutive Two-Step Parity-Pair Bound
(`sieveL2PrefixEnergy_moebiusReal_sub_add_two_second_band_le_two`):**
For every $n \ge 2$ and $M$ such that both steps $n + 1$ and $n + 2$ lie in the second band
($2(n + 2) \le M < 3(n + 1)$), exact parity alternation of $(n + 1, n + 2)$ implies that one
step is conserved ($= 0$) and the other is bounded by $2\mu(\text{even})^2 \le 2$, so:
$$\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+2}(M; \mu) \le 2$$
(an average downward growth of at most $1$ per step, matching the first band).
(Classification: Candidate new theorem.) -/
theorem sieveL2PrefixEnergy_moebiusReal_sub_add_two_second_band_le_two {n M : ℕ}
    (hn : 2 ≤ n) (hlo : 2 * (n + 2) ≤ M) (hhi : M < 3 * (n + 1)) :
    sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 2) M moebiusReal ≤ 2 := by
  rw [sieveL2PrefixEnergy_sub_add_two_eq]
  have hs1 := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_three_mul hn (by omega : M < 3 * (n + 1))
  have hs2 := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_lt_three_mul (by omega : 2 ≤ n + 1)
    (by omega : M < 3 * (n + 1 + 1))
  rw [if_neg (by omega : ¬ M < n + 1), if_neg (by omega : ¬ M < 2 * (n + 1))] at hs1
  rw [if_neg (by omega : ¬ M < n + 1 + 1), if_neg (by omega : ¬ M < 2 * (n + 1 + 1))] at hs2
  have hb1 := (moebiusReal_sq_bounds (n + 1)).2
  have hb2 := (moebiusReal_sq_bounds (n + 1 + 1)).2
  by_cases h2 : 2 ∣ n + 1
  · have hnot2 : ¬ 2 ∣ n + 1 + 1 := by omega
    rw [if_pos h2] at hs1
    rw [if_neg hnot2] at hs2
    linarith
  · have h2' : 2 ∣ n + 1 + 1 := by omega
    rw [if_neg h2] at hs1
    rw [if_pos h2'] at hs2
    linarith

/-- **Third-Band Consecutive Two-Step Parity-Pair Bound
(`sieveL2PrefixEnergy_moebiusReal_sub_add_two_third_band_le_four`):**
For every $n \ge 3$ and $M$ such that both steps $n + 1$ and $n + 2$ lie in the third band
($3(n + 2) \le M < 4(n + 1)$), exact parity alternation of $(n + 1, n + 2)$ bounds the even step
by $3\mu(\text{even})^2 \le 3$ and the odd step by $\mu(\text{odd})^2 \le 1$, yielding:
$$\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+2}(M; \mu) \le 4$$
(an average downward growth of at most $2$ per step across the third band, improving over the
single-step worst-case bound of $3$).
(Classification: Candidate new theorem.) -/
theorem sieveL2PrefixEnergy_moebiusReal_sub_add_two_third_band_le_four {n M : ℕ}
    (hn : 3 ≤ n) (hlo : 3 * (n + 2) ≤ M) (hhi : M < 4 * (n + 1)) :
    sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 2) M moebiusReal ≤ 4 := by
  rw [sieveL2PrefixEnergy_sub_add_two_eq]
  have hs1 := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_third_band hn (by omega) hhi
  have hs2 := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_third_band (by omega : 3 ≤ n + 1)
    hlo (by omega : M < 4 * (n + 1 + 1))
  have hb1_0 := (moebiusReal_sq_bounds (n + 1)).1
  have hb1_1 := (moebiusReal_sq_bounds (n + 1)).2
  have hb2_0 := (moebiusReal_sq_bounds (n + 1 + 1)).1
  have hb2_1 := (moebiusReal_sq_bounds (n + 1 + 1)).2
  by_cases h2 : 2 ∣ n + 1
  · have hnot2 : ¬ 2 ∣ n + 1 + 1 := by omega
    rw [if_pos h2] at hs1
    rw [if_neg hnot2] at hs2
    split_ifs at hs2 <;> linarith
  · have h2' : 2 ∣ n + 1 + 1 := by omega
    rw [if_neg h2] at hs1
    rw [if_pos h2'] at hs2
    split_ifs at hs1 <;> linarith

/-- **Third-Band $(2, 3)$-Coprime Squarefree Cancellation Bound
(`sieveL2PrefixEnergy_moebiusReal_sub_add_two_third_band_le_two_of_odd_coprime_three`):**
When $n \ge 3$, $3(n + 2) \le M < 4(n + 1)$, $2 \mid n + 1$, $\neg(3 \mid n + 2)$, and
$\operatorname{Squarefree}(n + 2)$ (for instance, whenever $p = n + 2 \ge 5$ is prime!), the
upward $+1$ step at $n + 2$ becomes a **downward $-1$ cancellation** against the even step $n + 1$,
giving:
$$\mathcal{E}_n(M; \mu) - \mathcal{E}_{n+2}(M; \mu)
  = 3\mu(n + 1)^2 - 1 \le 2$$
(reducing the average downward slope in the third band all the way to $1$ per step).
(Classification: Candidate new theorem.) -/
theorem sieveL2PrefixEnergy_moebiusReal_sub_add_two_third_band_le_two_of_odd_coprime_three
    {n M : ℕ} (hn : 3 ≤ n) (hlo : 3 * (n + 2) ≤ M) (hhi : M < 4 * (n + 1))
    (h2 : 2 ∣ n + 1) (hnot3 : ¬ 3 ∣ n + 2) (hsq : Squarefree (n + 2)) :
    sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 2) M moebiusReal =
        3 * moebiusReal (n + 1) ^ (2 : ℕ) - 1 ∧
      sieveL2PrefixEnergy n M moebiusReal - sieveL2PrefixEnergy (n + 2) M moebiusReal ≤ 2 := by
  have hs1 := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_third_band hn (by omega) hhi
  have hs2 := sieveL2PrefixEnergy_moebiusReal_succ_sub_of_third_band (by omega : 3 ≤ n + 1)
    hlo (by omega : M < 4 * (n + 1 + 1))
  have hnot2 : ¬ 2 ∣ n + 1 + 1 := by omega
  rw [if_pos h2] at hs1
  rw [if_neg hnot2, if_neg hnot3, moebiusReal_sq_eq_one_of_squarefree hsq] at hs2
  have hb1 := (moebiusReal_sq_bounds (n + 1)).2
  exact ⟨by linarith, by linarith⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
