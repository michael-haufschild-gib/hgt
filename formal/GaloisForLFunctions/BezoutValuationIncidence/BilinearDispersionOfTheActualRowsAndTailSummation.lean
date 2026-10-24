import GaloisForLFunctions.ArithmeticCompensationTheory.TheBalancedRegimeAndTheOmittedResidueClassLaw
import GaloisForLFunctions.BezoutValuationIncidence.TheReceiverEquivalenceAndZeroWidthLaw

/-!
# Bilinear Dispersion of the Actual Rows: Balanced Scales, Block-Mass Absorption, and Tail Summation

This module resolves Open Problem §7.4 ("Bilinear dispersion of the actual rows") of the
Bézout–Valuation Incidence programme (`BezoutValuationIncidence/README.md`) by proving:

1. **Universal Cauchy–Schwarz Absorption of Inverse-Prime Sums and Prime-Power Moments
   (`sum_abs_div_prime_le_sqrt_sum_sq_mul_sq`, `div_mul_sum_abs_div_prime_le_largeSieve`,
   `sum_abs_mul_sq_le_sqrt_sum_sq_mul_sq`, `sum_cube_le_sqrt_sum_sq`):**
   For every finite set of primes $S$ and every small-scale row $c$, Cauchy–Schwarz and
   $\sum_{p \in S} p^{-4} \le \sum_{p \in S} p^{-2} \le \pi^2/6 - 1 \le 1$ give the universal
   support-size-free inequality
   $$\sum_{p \in S} \frac{|c(p)|}{p} \le \sqrt{\sum_{p \in S} c(p)^2 p^2}, \qquad
     \sum_{p \in S} \frac{1}{p} \le \sqrt{\sum_{p \in S} p^2}.$$
   Combined with $\frac{1}{Q} = \sqrt{Q}\,Q^{-3/2} \le \sqrt{Q + 2 Q_0^2}\,Q^{-3/2}$, this absorbs
   the block-mass terms $|S'| \sum_{p \in S} |c(p)|/(6p)$ and $(1/6 + \pi^2/72)|S'| \sum_{p \in S} 1/p$
   into the leading $\varepsilon \sqrt{\sum_{p \in S} c(p)^2 p^2} \sqrt{Q + 2 Q_0^2}\,Q^{-3/2}$
   large-sieve factor at **every** scale $Q \ge 1$ and $Q_0 \ge 0$, without any leftover
   $\sum_{p \in S} 1/p$ remainder. Moreover, for $S \subseteq [1, Q_0]$, Cauchy–Schwarz bounds the
   quadratic and cubic prime sums by
   $$\sum_{p \in S} |c(p)| p^2 \le Q_0^{3/2} \sqrt{\sum_{p \in S} c(p)^2 p^2}, \qquad
     \sum_{p \in S} p^3 \le Q_0^{5/2} \sqrt{\sum_{p \in S} p^2}.$$

2. **Exact Log-Free Summation of the $n^{-3}$ and $n^{-4}$ Tails of the Möbius and Centred Prime
   Blocks (`sum_Icc_abs_moebiusWindowRow_div_cube_le`, `sum_Icc_abs_moebiusWindowRow_div_fourth_le`,
   `sum_Icc_abs_centredPrimeBlock_div_cube_le`, `sum_Icc_abs_centredPrimeBlock_div_fourth_le`,
   `eventually_sum_Icc_abs_centredPrimeBlock_div_cube_fourth_le`):**
   - For the Möbius block $\mu_Q = \mu \cdot \mathbf{1}_{(Q, 2Q]}$, for all $Q \ge 1$ and $N : \mathbb{N}$,
     $$\sum_{n=1}^N \frac{|\mu_Q(n)|}{n^3} \le \frac{1}{Q^2}, \qquad
       \sum_{n=1}^N \frac{|\mu_Q(n)|}{n^4} \le \frac{1}{Q^3}.$$
   - For the centred prime block $c'_Q = (\Lambda - 1) \cdot \mathbf{1}_{(Q, 2Q]}$, the pointwise
     identity $|\Lambda(n) - 1| \le (\Lambda(n) - 1) + 2$ avoids any logarithmic loss from
     $\Lambda(n) \le \log(2Q)$ and bounds the $n^{-3}$ and $n^{-4}$ tails for all $Q \ge 1$ and
     $N : \mathbb{N}$ by
     $$\sum_{n=1}^N \frac{|c'_Q(n)|}{n^3}
       \le \frac{1}{Q}\left|\sum_{Q < n \le 2Q} \frac{\Lambda(n) - 1}{n^2}\right| + \frac{2}{Q^2},
       \qquad
       \sum_{n=1}^N \frac{|c'_Q(n)|}{n^4}
       \le \frac{1}{Q^2}\left|\sum_{Q < n \le 2Q} \frac{\Lambda(n) - 1}{n^2}\right| + \frac{2}{Q^3},$$
     so eventually in $Q$ (for all $N : \mathbb{N}$),
     $$\sum_{n=1}^N \frac{|c'_Q(n)|}{n^3} \le \frac{3}{Q^2}, \qquad
       \sum_{n=1}^N \frac{|c'_Q(n)|}{n^4} \le \frac{3}{Q^3}.$$

3. **Block-Mass-Absorbed and Tail-Summed Bilinear and Dual-Norm Laws Across All Scales and in the
   Balanced Regime $P \le Q \le B P$ (`eventually_abs_rowBilinear_moebiusWindowRow_tail_summed_le`,
   `eventually_sum_abs_kernelStatistic_moebiusWindowRow_tail_summed_le`,
   `eventually_abs_rowBilinear_centredPrimeBlock_tail_summed_le`,
   `eventually_sum_abs_kernelStatistic_centredPrimeBlock_tail_summed_le`,
   `exists_balanced_centredPrimeBlock_rowBilinear_tail_summed_le`,
   `exists_balanced_centredPrimeBlock_dualNorm_tail_summed_le`):**
   Combining the $17/30$ short-window transfer (`TheBalancedRegimeAndTheOmittedResidueClassLaw`),
   universal inverse-prime absorption, and exact log-free tail summation eliminates the block-mass
   terms and sums the $n^{-3}, n^{-4}$ tails in all cross-scale bilinear and dual-norm bounds,
   including uniformly across the balanced regime $P \le Q \le B P$. Whenever $Q_0 \le \delta^2 Q$
   (every unbalanced scale $P = o(Q)$), the summed $n^{-3}$ and $n^{-4}$ tails are themselves
   absorbed into the single large-sieve term
   $\varepsilon \sqrt{\sum_{p \in S} c(p)^2 p^2} \sqrt{Q + 2 Q_0^2}\,Q^{-3/2}$
   (`eventually_moebiusWindowRow_pure_largeSieve_le`,
   `eventually_centredPrimeBlock_pure_largeSieve_le`).

4. **Equivalence of Quantitative Short-Window Power Savings with the Complete Coupled Receiver Below
   Half Damping (`primePowerWindowSaving_iff_all_receiver_forms`,
   `moebiusPowerWindowSaving_iff_all_receiver_forms`):**
   Upgrading the qualitative $o(1)$ short-window mean-square gain of the prime or Möbius row to a
   power saving at any fixed window exponent $\alpha \in (0, 1)$ is equivalent to crossing below
   half damping for the complete coupled receiver (`receiverDampingRate < 1 / 2`), to existence of
   some $\varepsilon \in (0, 1/2)$ in `receiverDampings` (or `interiorReceiverDampings`), and to the
   quasi-Riemann hypothesis $\Theta < 1$.
-/

open Finset Filter Topology RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.ArithmeticCompensationTheory
open ArithmeticFunction (vonMangoldt)
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Universal Cauchy–Schwarz Absorption of Inverse-Prime Sums and Prime-Power Moments -/

/-- For any finite set of primes `S`, `∑ p ∈ S, 1 / (p : ℝ) ^ 4 ≤ 1`. -/
theorem sum_inv_fourth_prime_le_one {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, 1 / (p : ℝ) ^ 4 ≤ 1 := by
  classical
  have h0S : 0 ∉ insert 1 S := by
    simp only [mem_insert, zero_ne_one, false_or]
    exact fun h => (hS 0 h).ne_zero rfl
  have h1S : 1 ∉ S := fun h => (hS 1 h).ne_one rfl
  have hzeta := sum_le_hasSum (insert 0 (insert 1 S)) (fun n _ => by positivity) hasSum_zeta_two
  rw [sum_insert h0S, sum_insert h1S] at hzeta
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    zero_add, Nat.cast_one, one_pow, div_one] at hzeta
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have hsq : ∑ p ∈ S, 1 / (p : ℝ) ^ 2 ≤ 1 := by linarith
  refine (sum_le_sum fun p hp => ?_).trans hsq
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hp1 (by norm_num))

/-- **Universal Cauchy–Schwarz Bound for Inverse-Prime Sums (`sum_abs_div_prime_le_sqrt_sum_sq_mul_sq`):**
For every finite set of primes `S` and every row `c : ℕ → ℝ`,
`∑ p ∈ S, |c p| / (p : ℝ) ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2)`. -/
theorem sum_abs_div_prime_le_sqrt_sum_sq_mul_sq {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (c : ℕ → ℝ) :
    ∑ p ∈ S, |c p| / (p : ℝ) ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) := by
  have heq : ∑ p ∈ S, |c p| / (p : ℝ) = ∑ p ∈ S, (|c p| * (p : ℝ)) * (1 / (p : ℝ) ^ 2) := by
    refine sum_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
    field_simp
  rw [heq]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S (fun p => |c p| * (p : ℝ)) (fun p => 1 / (p : ℝ) ^ 2)
  have h1 : ∑ p ∈ S, (|c p| * (p : ℝ)) ^ 2 = ∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2 :=
    sum_congr rfl fun p _ => by rw [mul_pow, sq_abs]
  have h2 : Real.sqrt (∑ p ∈ S, (1 / (p : ℝ) ^ 2) ^ 2) ≤ 1 := by
    rw [← Real.sqrt_one]
    refine Real.sqrt_le_sqrt ?_
    refine (le_of_eq (sum_congr rfl fun p _ => ?_)).trans (sum_inv_fourth_prime_le_one hS)
    ring
  rw [h1] at hcs
  calc ∑ p ∈ S, (|c p| * (p : ℝ)) * (1 / (p : ℝ) ^ 2)
      ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
          Real.sqrt (∑ p ∈ S, (1 / (p : ℝ) ^ 2) ^ 2) := hcs
    _ ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) := mul_one _

/-- For every finite set of primes `S`, `∑ p ∈ S, 1 / (p : ℝ) ≤ Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2)`. -/
theorem sum_one_div_prime_le_sqrt_sum_sq {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, 1 / (p : ℝ) ≤ Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) := by
  simpa using sum_abs_div_prime_le_sqrt_sum_sq_mul_sq hS (fun _ => 1)

/-- For `Q ≥ 1` and `K ≥ 0`, `1 / (Q : ℝ) ≤ Real.sqrt ((Q : ℝ) + K) * Real.sqrt (1 / (Q : ℝ) ^ 3)`. -/
theorem one_div_le_sqrt_add_mul_sqrt_inv_cube {Q : ℕ} (hQ : 1 ≤ Q) {K : ℝ} (hK : 0 ≤ K) :
    1 / (Q : ℝ) ≤ Real.sqrt ((Q : ℝ) + K) * Real.sqrt (1 / (Q : ℝ) ^ 3) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h1 : 1 / (Q : ℝ) = Real.sqrt (Q : ℝ) * Real.sqrt (1 / (Q : ℝ) ^ 3) := by
    rw [← Real.sqrt_mul hQ0.le,
      show (Q : ℝ) * (1 / (Q : ℝ) ^ 3) = (1 / (Q : ℝ)) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
  rw [h1]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)

/-- **Block-Mass Absorption into the Large-Sieve Scale (`div_mul_sum_abs_div_prime_le_largeSieve`):**
For every finite set of primes `S`, row `c : ℕ → ℝ`, `Q ≥ 1`, and `K ≥ 0`,
`(1 / (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ) ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt ((Q : ℝ) + K) * Real.sqrt (1 / (Q : ℝ) ^ 3)`. -/
theorem div_mul_sum_abs_div_prime_le_largeSieve {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (c : ℕ → ℝ) {Q : ℕ} (hQ : 1 ≤ Q) {K : ℝ} (hK : 0 ≤ K) :
    (1 / (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ) ≤
      Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
        Real.sqrt ((Q : ℝ) + K) * Real.sqrt (1 / (Q : ℝ) ^ 3) := by
  have h1 := sum_abs_div_prime_le_sqrt_sum_sq_mul_sq hS c
  have h2 := one_div_le_sqrt_add_mul_sqrt_inv_cube hQ hK
  calc (1 / (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ)
      ≤ (Real.sqrt ((Q : ℝ) + K) * Real.sqrt (1 / (Q : ℝ) ^ 3)) *
          Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) :=
        mul_le_mul h2 h1 (sum_nonneg fun _ _ => by positivity) (by positivity)
    _ = _ := by ring

/-- Numerical bound `(1 / 6 + Real.pi ^ 2 / 72) * Real.sqrt 2 ≤ 1 / 2`. -/
theorem one_div_six_add_pi_sq_div_72_mul_sqrt_two_le_half :
    (1 / 6 + Real.pi ^ 2 / 72) * Real.sqrt 2 ≤ 1 / 2 := by
  have hpi := Real.pi_lt_d2
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos]
  nlinarith [Real.sqrt_nonneg 2]

/-- Numerical bound `Real.sqrt 2 / 6 ≤ 1 / 2`. -/
theorem sqrt_two_div_six_le_half : Real.sqrt 2 / 6 ≤ 1 / 2 := by
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- For any `S ⊆ Icc 1 Q₀`, `∑ p ∈ S, (p : ℝ) ^ 2 ≤ (Q₀ : ℝ) ^ 3`. -/
theorem sum_sq_le_cube_of_le {S : Finset ℕ} {Q₀ : ℕ}
    (hS : ∀ p ∈ S, 1 ≤ p ∧ p ≤ Q₀) :
    ∑ p ∈ S, (p : ℝ) ^ 2 ≤ (Q₀ : ℝ) ^ 3 := by
  have hsub : S ⊆ Icc 1 Q₀ := fun p hp => mem_Icc.mpr (hS p hp)
  have hcard : (S.card : ℝ) ≤ Q₀ := by
    have := card_le_card hsub
    rw [Nat.card_Icc, show Q₀ + 1 - 1 = Q₀ by omega] at this
    exact_mod_cast this
  calc ∑ p ∈ S, (p : ℝ) ^ 2
      ≤ ∑ _p ∈ S, (Q₀ : ℝ) ^ 2 := by
        refine sum_le_sum fun p hp => ?_
        have hpQ : (p : ℝ) ≤ Q₀ := by exact_mod_cast (hS p hp).2
        exact pow_le_pow_left₀ (Nat.cast_nonneg p) hpQ 2
    _ = (S.card : ℝ) * (Q₀ : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Q₀ : ℝ) * (Q₀ : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (Q₀ : ℝ) ^ 3 := by ring

/-- For any `S ⊆ Icc 1 Q₀` and `c : ℕ → ℝ` supported on `S`,
`∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 ≤ Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2)`. -/
theorem sum_Icc_abs_mul_sq_le_sqrt_sum_sq_mul_sq {N Q₀ : ℕ} {S : Finset ℕ}
    (hSN : ∀ p ∈ S, 1 ≤ p ∧ p ≤ N ∧ p ≤ Q₀) {c : ℕ → ℝ} (hsupp : ∀ d, c d ≠ 0 → d ∈ S) :
    ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 ≤
      Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) := by
  have hsub : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr ⟨(hSN p hp).1, (hSN p hp).2.1⟩
  rw [← sum_subset hsub fun d _ hd => by
    have : c d = 0 := by by_contra h; exact hd (hsupp d h)
    simp [this]]
  have heq : ∑ p ∈ S, |c p| * (p : ℝ) ^ 2 = ∑ p ∈ S, (|c p| * (p : ℝ)) * (p : ℝ) :=
    sum_congr rfl fun p _ => by ring
  rw [heq]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S (fun p => |c p| * (p : ℝ)) (fun p => (p : ℝ))
  have h1 : ∑ p ∈ S, (|c p| * (p : ℝ)) ^ 2 = ∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2 :=
    sum_congr rfl fun p _ => by rw [mul_pow, sq_abs]
  have h2 : Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) ≤ Real.sqrt ((Q₀ : ℝ) ^ 3) :=
    Real.sqrt_le_sqrt (sum_sq_le_cube_of_le fun p hp => ⟨(hSN p hp).1, (hSN p hp).2.2⟩)
  rw [h1] at hcs
  calc ∑ p ∈ S, (|c p| * (p : ℝ)) * (p : ℝ)
      ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) := hcs
    _ ≤ Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt ((Q₀ : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

/-- For any `S ⊆ Icc 1 Q₀`,
`∑ p ∈ S, (p : ℝ) ^ 2 ≤ Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2)` and
`∑ p ∈ S, (p : ℝ) ^ 3 ≤ (Q₀ : ℝ) * Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2)`. -/
theorem sum_sq_and_cube_le_sqrt_sum_sq {Q₀ : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, 1 ≤ p ∧ p ≤ Q₀) :
    ∑ p ∈ S, (p : ℝ) ^ 2 ≤ Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) ∧
    ∑ p ∈ S, (p : ℝ) ^ 3 ≤
      (Q₀ : ℝ) * Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) := by
  have h0 : 0 ≤ ∑ p ∈ S, (p : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h1 : Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) ≤ Real.sqrt ((Q₀ : ℝ) ^ 3) :=
    Real.sqrt_le_sqrt (sum_sq_le_cube_of_le hS)
  have hsq : ∑ p ∈ S, (p : ℝ) ^ 2 ≤
      Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) := by
    calc ∑ p ∈ S, (p : ℝ) ^ 2
        = Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) :=
          (Real.mul_self_sqrt h0).symm
      _ ≤ Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
  refine ⟨hsq, ?_⟩
  calc ∑ p ∈ S, (p : ℝ) ^ 3
      ≤ ∑ p ∈ S, (Q₀ : ℝ) * (p : ℝ) ^ 2 := by
        refine sum_le_sum fun p hp => ?_
        have hpQ : (p : ℝ) ≤ Q₀ := by exact_mod_cast (hS p hp).2
        calc (p : ℝ) ^ 3 = (p : ℝ) * (p : ℝ) ^ 2 := by ring
          _ ≤ (Q₀ : ℝ) * (p : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hpQ (sq_nonneg _)
    _ = (Q₀ : ℝ) * ∑ p ∈ S, (p : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ (Q₀ : ℝ) * (Real.sqrt ((Q₀ : ℝ) ^ 3) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg Q₀)
    _ = _ := by ring

/-! ## §2. Exact Log-Free Summation of the `n⁻³` and `n⁻⁴` Tails of the Actual Rows -/

/-- **Exact Summation of the `n⁻³` Tail of the Möbius Block (`sum_Icc_abs_moebiusWindowRow_div_cube_le`):**
For every `Q ≥ 1` and `N : ℕ`, `∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 ≤ 1 / (Q : ℝ) ^ 2`. -/
theorem sum_Icc_abs_moebiusWindowRow_div_cube_le {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ) :
    ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 ≤ 1 / (Q : ℝ) ^ 2 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsub : (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q) ⊆ Ioc Q (2 * Q) := fun n hn =>
    mem_Ioc.mpr (mem_filter.mp hn).2
  have heq : ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 =
      ∑ n ∈ (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q), |moebiusReal n| / (n : ℝ) ^ 3 := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    unfold moebiusWindowRow
    split_ifs <;> simp
  rw [heq]
  calc ∑ n ∈ (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q), |moebiusReal n| / (n : ℝ) ^ 3
      ≤ ∑ n ∈ Ioc Q (2 * Q), |moebiusReal n| / (n : ℝ) ^ 3 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ _n ∈ Ioc Q (2 * Q), 1 / (Q : ℝ) ^ 3 := by
        refine sum_le_sum fun n hn => ?_
        have hnQ : (Q : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
        calc |moebiusReal n| / (n : ℝ) ^ 3
            ≤ 1 / (n : ℝ) ^ 3 :=
              div_le_div_of_nonneg_right (abs_moebiusReal_le_one' n) (by positivity)
          _ ≤ 1 / (Q : ℝ) ^ 3 :=
              one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hQ0.le hnQ 3)
    _ = 1 / (Q : ℝ) ^ 2 := by
        rw [sum_const, Nat.card_Ioc, show 2 * Q - Q = Q by omega, nsmul_eq_mul]
        field_simp

/-- **Exact Summation of the `n⁻⁴` Tail of the Möbius Block (`sum_Icc_abs_moebiusWindowRow_div_fourth_le`):**
For every `Q ≥ 1` and `N : ℕ`, `∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 4 ≤ 1 / (Q : ℝ) ^ 3`. -/
theorem sum_Icc_abs_moebiusWindowRow_div_fourth_le {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ) :
    ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 4 ≤ 1 / (Q : ℝ) ^ 3 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsub : (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q) ⊆ Ioc Q (2 * Q) := fun n hn =>
    mem_Ioc.mpr (mem_filter.mp hn).2
  have heq : ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 4 =
      ∑ n ∈ (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q), |moebiusReal n| / (n : ℝ) ^ 4 := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    unfold moebiusWindowRow
    split_ifs <;> simp
  rw [heq]
  calc ∑ n ∈ (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q), |moebiusReal n| / (n : ℝ) ^ 4
      ≤ ∑ n ∈ Ioc Q (2 * Q), |moebiusReal n| / (n : ℝ) ^ 4 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ _n ∈ Ioc Q (2 * Q), 1 / (Q : ℝ) ^ 4 := by
        refine sum_le_sum fun n hn => ?_
        have hnQ : (Q : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
        calc |moebiusReal n| / (n : ℝ) ^ 4
            ≤ 1 / (n : ℝ) ^ 4 :=
              div_le_div_of_nonneg_right (abs_moebiusReal_le_one' n) (by positivity)
          _ ≤ 1 / (Q : ℝ) ^ 4 :=
              one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hQ0.le hnQ 4)
    _ = 1 / (Q : ℝ) ^ 3 := by
        rw [sum_const, Nat.card_Ioc, show 2 * Q - Q = Q by omega, nsmul_eq_mul]
        field_simp

/-- **Log-Free `n⁻²` Absolute Sum of the Centred Prime Block (`sum_Ioc_abs_centredPrimeBlock_div_sq_le`):**
Because `vonMangoldt n ≥ 0`, `|vonMangoldt n - 1| ≤ (vonMangoldt n - 1) + 2`, so for every `Q ≥ 1`,
`∑ n ∈ Ioc Q (2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 2 ≤ |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| + 2 / (Q : ℝ)`. -/
theorem sum_Ioc_abs_centredPrimeBlock_div_sq_le {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ n ∈ Ioc Q (2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 2 ≤
      |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| + 2 / (Q : ℝ) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpt : ∀ n ∈ Ioc Q (2 * Q),
      |vonMangoldt n - 1| / (n : ℝ) ^ 2 ≤
        (vonMangoldt n - 1) / (n : ℝ) ^ 2 + 2 * (1 / (n : ℝ) ^ 2) := by
    intro n _
    have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have habs : |vonMangoldt n - 1| ≤ (vonMangoldt n - 1) + 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    calc |vonMangoldt n - 1| / (n : ℝ) ^ 2
        ≤ ((vonMangoldt n - 1) + 2) / (n : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right habs (by positivity)
      _ = (vonMangoldt n - 1) / (n : ℝ) ^ 2 + 2 * (1 / (n : ℝ) ^ 2) := by ring
  have hmass : ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 2 ≤ 1 / (Q : ℝ) :=
    (dyadicInverseSquareMass_le Q).trans (one_div_le_one_div_of_le hQ0 (by linarith))
  calc ∑ n ∈ Ioc Q (2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Ioc Q (2 * Q), ((vonMangoldt n - 1) / (n : ℝ) ^ 2 + 2 * (1 / (n : ℝ) ^ 2)) :=
        sum_le_sum hpt
    _ = ∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2 +
          2 * ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 2 := by
        rw [sum_add_distrib, ← mul_sum]
    _ ≤ |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| + 2 * (1 / (Q : ℝ)) :=
        add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_left hmass zero_le_two)
    _ = _ := by ring

/-- **Log-Free `n⁻³` Tail Bound for the Centred Prime Block (`sum_Icc_abs_centredPrimeBlock_div_cube_le`):**
For every `Q ≥ 1` and `N : ℕ`,
`∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 ≤ |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / (Q : ℝ) + 2 / (Q : ℝ) ^ 2`. -/
theorem sum_Icc_abs_centredPrimeBlock_div_cube_le {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ) :
    ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 ≤
      |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / (Q : ℝ) + 2 / (Q : ℝ) ^ 2 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsub : (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q) ⊆ Ioc Q (2 * Q) := fun n hn =>
    mem_Ioc.mpr (mem_filter.mp hn).2
  have heq : ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 =
      ∑ n ∈ (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 3 := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    unfold centredPrimeBlock
    split_ifs <;> simp
  rw [heq]
  calc ∑ n ∈ (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 3
      ≤ ∑ n ∈ Ioc Q (2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 3 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ n ∈ Ioc Q (2 * Q), (1 / (Q : ℝ)) * (|vonMangoldt n - 1| / (n : ℝ) ^ 2) := by
        refine sum_le_sum fun n hn => ?_
        have hnQ : (Q : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
        have hn0 : (0 : ℝ) < n := by linarith
        rw [show |vonMangoldt n - 1| / (n : ℝ) ^ 3 =
            (1 / (n : ℝ)) * (|vonMangoldt n - 1| / (n : ℝ) ^ 2) by ring]
        exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hQ0 hnQ) (by positivity)
    _ = (1 / (Q : ℝ)) * ∑ n ∈ Ioc Q (2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 2 :=
        (mul_sum _ _ _).symm
    _ ≤ (1 / (Q : ℝ)) *
          (|∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| + 2 / (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_abs_centredPrimeBlock_div_sq_le hQ) (by positivity)
    _ = _ := by ring

/-- **Log-Free `n⁻⁴` Tail Bound for the Centred Prime Block (`sum_Icc_abs_centredPrimeBlock_div_fourth_le`):**
For every `Q ≥ 1` and `N : ℕ`,
`∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 ≤ |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / (Q : ℝ) ^ 2 + 2 / (Q : ℝ) ^ 3`. -/
theorem sum_Icc_abs_centredPrimeBlock_div_fourth_le {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ) :
    ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 ≤
      |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / (Q : ℝ) ^ 2 + 2 / (Q : ℝ) ^ 3 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsub : (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q) ⊆ Ioc Q (2 * Q) := fun n hn =>
    mem_Ioc.mpr (mem_filter.mp hn).2
  have heq : ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 =
      ∑ n ∈ (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 4 := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    unfold centredPrimeBlock
    split_ifs <;> simp
  rw [heq]
  calc ∑ n ∈ (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 4
      ≤ ∑ n ∈ Ioc Q (2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 4 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ n ∈ Ioc Q (2 * Q), (1 / (Q : ℝ) ^ 2) * (|vonMangoldt n - 1| / (n : ℝ) ^ 2) := by
        refine sum_le_sum fun n hn => ?_
        have hnQ : (Q : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
        rw [show |vonMangoldt n - 1| / (n : ℝ) ^ 4 =
            (1 / (n : ℝ) ^ 2) * (|vonMangoldt n - 1| / (n : ℝ) ^ 2) by ring]
        exact mul_le_mul_of_nonneg_right
          (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hQ0.le hnQ 2)) (by positivity)
    _ = (1 / (Q : ℝ) ^ 2) * ∑ n ∈ Ioc Q (2 * Q), |vonMangoldt n - 1| / (n : ℝ) ^ 2 :=
        (mul_sum _ _ _).symm
    _ ≤ (1 / (Q : ℝ) ^ 2) *
          (|∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| + 2 / (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_abs_centredPrimeBlock_div_sq_le hQ) (by positivity)
    _ = _ := by ring

/-- **Eventual Log-Free `3 / Q²` and `3 / Q³` Tail Bounds for the Centred Prime Block
(`eventually_sum_Icc_abs_centredPrimeBlock_div_cube_fourth_le`):**
For all sufficiently large `Q`, uniformly in `N : ℕ`,
`∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 ≤ 3 / (Q : ℝ) ^ 2` and
`∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 ≤ 3 / (Q : ℝ) ^ 3`. -/
theorem eventually_sum_Icc_abs_centredPrimeBlock_div_cube_fourth_le :
    ∀ᶠ Q : ℕ in atTop, ∀ N : ℕ,
      ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 ≤ 3 / (Q : ℝ) ^ 2 ∧
      ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 ≤ 3 / (Q : ℝ) ^ 3 := by
  have hα : (17 / 30 : ℝ) < 2 / 3 := by norm_num
  have hα1 : (2 / 3 : ℝ) < 1 := by norm_num
  have hε0 : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  filter_upwards [eventually_centredPrimeBlock_average_le_seventeenThirtieths hα hα1 hε0,
    eventually_ge_atTop 1] with Q hQ hQ1 N
  have hmass : |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| ≤ 1 / (Q : ℝ) := by
    have h := hQ.2.2.2
    rw [mul_one_div_cancel (Real.sqrt_pos.mpr zero_lt_two).ne'] at h
    exact h
  have h3 := sum_Icc_abs_centredPrimeBlock_div_cube_le hQ1 N
  have h4 := sum_Icc_abs_centredPrimeBlock_div_fourth_le hQ1 N
  have hc1 :
      |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / (Q : ℝ) + 2 / (Q : ℝ) ^ 2 ≤
        3 / (Q : ℝ) ^ 2 := by
    have hd : |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / (Q : ℝ) ≤
        (1 / (Q : ℝ)) / (Q : ℝ) := div_le_div_of_nonneg_right hmass (Nat.cast_nonneg Q)
    calc _ ≤ (1 / (Q : ℝ)) / (Q : ℝ) + 2 / (Q : ℝ) ^ 2 := add_le_add hd le_rfl
      _ = 3 / (Q : ℝ) ^ 2 := by ring
  have hc2 :
      |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / (Q : ℝ) ^ 2 + 2 / (Q : ℝ) ^ 3 ≤
        3 / (Q : ℝ) ^ 3 := by
    have hd : |∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n - 1) / (n : ℝ) ^ 2| / (Q : ℝ) ^ 2 ≤
        (1 / (Q : ℝ)) / (Q : ℝ) ^ 2 := div_le_div_of_nonneg_right hmass (by positivity)
    calc _ ≤ (1 / (Q : ℝ)) / (Q : ℝ) ^ 2 + 2 / (Q : ℝ) ^ 3 := add_le_add hd le_rfl
      _ = 3 / (Q : ℝ) ^ 3 := by ring
  exact ⟨h3.trans hc1, h4.trans hc2⟩

/-! ## §3. Block-Mass-Absorbed and Tail-Summed Bilinear and Dual-Norm Laws -/

/-- **Block-Mass-Absorbed and Tail-Summed Cross-Scale Bound for the Möbius Block
(`eventually_abs_rowBilinear_moebiusWindowRow_tail_summed_le`):**
For every `ε > 0` and all large `Q`, every row `c` on primes `p ∈ S ⊆ [1, min(N, Q₀)]` with
`8 log₂ Q ≤ ε² p` has its block-mass term absorbed into the leading `ε`-large-sieve term and its
`n⁻³` tail summed to `3 / (4 Q²) * ∑ d ∈ Icc 1 N, |c d| d²`. -/
theorem eventually_abs_rowBilinear_moebiusWindowRow_tail_summed_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}, 2 ≤ Q₀ →
      Q + Q + Nat.log 2 Q ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (Nat.log 2 Q : ℝ) ≤ (ε / 2) ^ 2 * p) → (∀ n, c n ≠ 0 → n ∈ S) →
      |rowBilinear N c (moebiusWindowRow Q) +
          rowMean N c * vonMangoldtReadout N (moebiusWindowRow Q) +
          rowBeta N c * finiteHarmonicSum N (moebiusWindowRow Q)| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
            Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) +
          3 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := by
  filter_upwards [eventually_abs_rowBilinear_moebiusWindowRow_le_eliminated (half_pos hε),
    eventually_ge_atTop 1] with Q hQ hQ1
  intro N Q₀ S c hQ₀ hN hS hSP hsupp
  have h1 := hQ hQ₀ hN hS hSP hsupp
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have habs := div_mul_sum_abs_div_prime_le_largeSieve hSp c hQ1
    (by positivity : (0 : ℝ) ≤ 2 * (Q₀ : ℝ) ^ 2)
  have hmass :
      Real.sqrt 2 * (ε / 2) / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ) ≤
        (ε / 2) * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
          Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) := by
    have hcoeff : Real.sqrt 2 / 6 ≤ 1 := by linarith [sqrt_two_div_six_le_half]
    calc Real.sqrt 2 * (ε / 2) / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ)
        = (Real.sqrt 2 / 6) * (ε / 2) * ((1 / (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ)) := by ring
      _ ≤ 1 * (ε / 2) *
            (Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
              Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (by positivity)) habs
            (by positivity) (by positivity)
      _ = _ := by ring
  have htail :
      3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
          ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 ≤
        3 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := by
    have hc0 : 0 ≤ 3 / 4 * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => by positivity)
    calc 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3
        ≤ 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * (1 / (Q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_Icc_abs_moebiusWindowRow_div_cube_le hQ1 N) hc0
      _ = _ := by ring
  linarith

/-- **Block-Mass-Absorbed and Tail-Summed Dual-Norm Bound for the Möbius Block
(`eventually_sum_abs_kernelStatistic_moebiusWindowRow_tail_summed_le`):**
For every `ε > 0` and all large `Q`, every prime set `S ⊆ [1, min(N, Q₀)]` with
`8 log₂ Q ≤ (ε/2)² p` satisfies
`∑ p ∈ S, |kernelStatistic N (moebiusWindowRow Q) p| / p ≤ ε √(∑ p²) √(Q + 2Q₀²) Q^{-3/2} + 3/(4Q²) ∑ p² + 6/Q³ ∑ p³`. -/
theorem eventually_sum_abs_kernelStatistic_moebiusWindowRow_tail_summed_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ}, 2 ≤ Q₀ →
      Q + Q + Nat.log 2 Q ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (Nat.log 2 Q : ℝ) ≤ (ε / 2) ^ 2 * p) →
      ∑ p ∈ S, |kernelStatistic N (moebiusWindowRow Q) p| / p ≤
        ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
            (Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) +
          3 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2) +
          6 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3) := by
  filter_upwards [eventually_sum_abs_kernelStatistic_moebiusWindowRow_le_eliminated (half_pos hε),
    eventually_ge_atTop 1] with Q hQ hQ1
  intro N Q₀ S hQ₀ hN hS hSP
  have h1 := hQ hQ₀ hN hS hSP
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have habs := div_mul_sum_abs_div_prime_le_largeSieve hSp (fun _ => 1) hQ1
    (by positivity : (0 : ℝ) ≤ 2 * (Q₀ : ℝ) ^ 2)
  simp only [abs_one, one_pow, one_mul] at habs
  have hmass :
      (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * (ε / 2) / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ) ≤
        (ε / 2) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
          (Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) := by
    have hcoeff : (1 / 6 + Real.pi ^ 2 / 72) * Real.sqrt 2 ≤ 1 := by
      linarith [one_div_six_add_pi_sq_div_72_mul_sqrt_two_le_half]
    calc (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * (ε / 2) / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ)
        = ((1 / 6 + Real.pi ^ 2 / 72) * Real.sqrt 2) * (ε / 2) *
            ((1 / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ)) := by ring
      _ ≤ 1 * (ε / 2) *
            (Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
              Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (by positivity)) habs
            (by positivity) (by positivity)
      _ = _ := by ring
  have htail3 :
      3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3 ≤
        3 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2) := by
    have hc0 : 0 ≤ 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => sq_nonneg _)
    calc 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 3
        ≤ 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * (1 / (Q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_Icc_abs_moebiusWindowRow_div_cube_le hQ1 N) hc0
      _ = _ := by ring
  have htail4 :
      6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 4 ≤
        6 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3) := by
    have hc0 : 0 ≤ 6 * (∑ p ∈ S, (p : ℝ) ^ 3) :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => by positivity)
    calc 6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 4
        ≤ 6 * (∑ p ∈ S, (p : ℝ) ^ 3) * (1 / (Q : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left (sum_Icc_abs_moebiusWindowRow_div_fourth_le hQ1 N) hc0
      _ = _ := by ring
  linarith

/-- **Block-Mass-Absorbed and Log-Free Tail-Summed Cross-Scale Bound for the Centred Prime Block
(`eventually_abs_rowBilinear_centredPrimeBlock_tail_summed_le`):**
For every `17/30 < α < 1` and `ε > 0`, eventually in `Q`, the block-mass term of the centred prime
block is absorbed into the leading `ε`-large-sieve term and its `n⁻³` tail is summed without
logarithmic loss to `9 / (4 Q²) * ∑ d ∈ Icc 1 N, |c d| d²`. -/
theorem eventually_abs_rowBilinear_centredPrimeBlock_tail_summed_le {α : ℝ}
    (hα : 17 / 30 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}, 2 ≤ Q₀ →
      Q + Q + ⌈(2 * (Q : ℝ)) ^ α⌉₊ ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤ (ε / 2) ^ 2 * p) →
      (∀ n, c n ≠ 0 → n ∈ S) →
      |rowBilinear N c (centredPrimeBlock Q) +
          rowMean N c * vonMangoldtReadout N (centredPrimeBlock Q) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeBlock Q)| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
            Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) +
          9 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := by
  filter_upwards [eventually_abs_rowBilinear_centredPrimeBlock_le_seventeenThirtieths hα hα1
      (half_pos hε),
    eventually_sum_Icc_abs_centredPrimeBlock_div_cube_fourth_le,
    eventually_ge_atTop 1] with Q hQ htailQ hQ1
  intro N Q₀ S c hQ₀ hN hS hSP hsupp
  have h1 := hQ hQ₀ hN hS hSP hsupp
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have habs := div_mul_sum_abs_div_prime_le_largeSieve hSp c hQ1
    (by positivity : (0 : ℝ) ≤ 2 * (Q₀ : ℝ) ^ 2)
  have hmass :
      Real.sqrt 2 * (ε / 2) / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ) ≤
        (ε / 2) * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
          Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) := by
    have hcoeff : Real.sqrt 2 / 6 ≤ 1 := by linarith [sqrt_two_div_six_le_half]
    calc Real.sqrt 2 * (ε / 2) / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ)
        = (Real.sqrt 2 / 6) * (ε / 2) * ((1 / (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ)) := by ring
      _ ≤ 1 * (ε / 2) *
            (Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
              Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (by positivity)) habs
            (by positivity) (by positivity)
      _ = _ := by ring
  have htail :
      3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
          ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 ≤
        9 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := by
    have hc0 : 0 ≤ 3 / 4 * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => by positivity)
    calc 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3
        ≤ 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * (3 / (Q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (htailQ N).1 hc0
      _ = _ := by ring
  linarith

/-- **Block-Mass-Absorbed and Log-Free Tail-Summed Dual-Norm Bound for the Centred Prime Block
(`eventually_sum_abs_kernelStatistic_centredPrimeBlock_tail_summed_le`):**
For every `17/30 < α < 1` and `ε > 0`, eventually in `Q`,
`∑ p ∈ S, |kernelStatistic N (centredPrimeBlock Q) p| / p ≤ ε √(∑ p²) √(Q + 2Q₀²) Q^{-3/2} + 9/(4Q²) ∑ p² + 18/Q³ ∑ p³`. -/
theorem eventually_sum_abs_kernelStatistic_centredPrimeBlock_tail_summed_le {α : ℝ}
    (hα : 17 / 30 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ}, 2 ≤ Q₀ →
      Q + Q + ⌈(2 * (Q : ℝ)) ^ α⌉₊ ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤ (ε / 2) ^ 2 * p) →
      ∑ p ∈ S, |kernelStatistic N (centredPrimeBlock Q) p| / p ≤
        ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
            (Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) +
          9 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2) +
          18 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3) := by
  filter_upwards [eventually_sum_abs_kernelStatistic_centredPrimeBlock_le_seventeenThirtieths hα hα1
      (half_pos hε),
    eventually_sum_Icc_abs_centredPrimeBlock_div_cube_fourth_le,
    eventually_ge_atTop 1] with Q hQ htailQ hQ1
  intro N Q₀ S hQ₀ hN hS hSP
  have h1 := hQ hQ₀ hN hS hSP
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have habs := div_mul_sum_abs_div_prime_le_largeSieve hSp (fun _ => 1) hQ1
    (by positivity : (0 : ℝ) ≤ 2 * (Q₀ : ℝ) ^ 2)
  simp only [abs_one, one_pow, one_mul] at habs
  have hmass :
      (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * (ε / 2) / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ) ≤
        (ε / 2) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
          (Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) := by
    have hcoeff : (1 / 6 + Real.pi ^ 2 / 72) * Real.sqrt 2 ≤ 1 := by
      linarith [one_div_six_add_pi_sq_div_72_mul_sqrt_two_le_half]
    calc (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * (ε / 2) / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ)
        = ((1 / 6 + Real.pi ^ 2 / 72) * Real.sqrt 2) * (ε / 2) *
            ((1 / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ)) := by ring
      _ ≤ 1 * (ε / 2) *
            (Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
              Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (by positivity)) habs
            (by positivity) (by positivity)
      _ = _ := by ring
  have htail3 :
      3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 ≤
        9 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2) := by
    have hc0 : 0 ≤ 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => sq_nonneg _)
    calc 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3
        ≤ 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * (3 / (Q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (htailQ N).1 hc0
      _ = _ := by ring
  have htail4 :
      6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 ≤
        18 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3) := by
    have hc0 : 0 ≤ 6 * (∑ p ∈ S, (p : ℝ) ^ 3) :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => by positivity)
    calc 6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4
        ≤ 6 * (∑ p ∈ S, (p : ℝ) ^ 3) * (3 / (Q : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left (htailQ N).2 hc0
      _ = _ := by ring
  linarith

/-- **Uniform Balanced-Regime Bilinear Law with Block-Mass Absorption and Tail Summation
(`exists_balanced_centredPrimeBlock_rowBilinear_tail_summed_le`):**
For every aspect ratio `B ≥ 1` and `ε > 0`, there exists `P₀ : ℕ` such that for all `P ≥ P₀`,
`P ≤ Q ≤ B P`, `3 Q ≤ N`, and `S ⊆ (P, 2P]` of primes with `2P ≤ N`:
`|B(c, c'_Q) + m(c) R(c'_Q) + β(c) H(c'_Q)| ≤ ε √(∑ c(p)² p²) √(Q + 8P²) Q^{-3/2} + 9/(4Q²) ∑ |c(d)| d²`. -/
theorem exists_balanced_centredPrimeBlock_rowBilinear_tail_summed_le
    {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ {N P Q : ℕ} {S : Finset ℕ} {c : ℕ → ℝ}, P₀ ≤ P → P ≤ Q → (Q : ℝ) ≤ B * P →
      3 * Q ≤ N → (∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 2 * P ∧ p ≤ N) →
      (∀ n, c n ≠ 0 → n ∈ S) →
      |rowBilinear N c (centredPrimeBlock Q) +
          rowMean N c * vonMangoldtReadout N (centredPrimeBlock Q) +
          rowBeta N c * finiteHarmonicSum N (centredPrimeBlock Q)| ≤
        ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
            Real.sqrt ((Q : ℝ) + 8 * (P : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) +
          9 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := by
  obtain ⟨P₁, hP₁⟩ := exists_balanced_centredPrimeBlock_rowBilinear_le hB (half_pos hε)
  obtain ⟨Q₂, hQ₂⟩ := eventually_atTop.mp
    eventually_sum_Icc_abs_centredPrimeBlock_div_cube_fourth_le
  refine ⟨max P₁ (max Q₂ 1), ?_⟩
  intro N P Q S c hP hPQ hQB hN hS hsupp
  have hP' : P₁ ≤ P := (le_max_left _ _).trans hP
  have hQ1 : 1 ≤ Q := ((le_max_right _ _).trans ((le_max_right _ _).trans hP)).trans hPQ
  have hQ' : Q₂ ≤ Q := ((le_max_left _ _).trans ((le_max_right _ _).trans hP)).trans hPQ
  have h1 := hP₁ hP' hPQ hQB hN hS hsupp
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have habs := div_mul_sum_abs_div_prime_le_largeSieve hSp c hQ1
    (by positivity : (0 : ℝ) ≤ 8 * (P : ℝ) ^ 2)
  have hmass :
      Real.sqrt 2 * (ε / 2) / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ) ≤
        (ε / 2) * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
          Real.sqrt ((Q : ℝ) + 8 * (P : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) := by
    have hcoeff : Real.sqrt 2 / 6 ≤ 1 := by linarith [sqrt_two_div_six_le_half]
    calc Real.sqrt 2 * (ε / 2) / (6 * (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ)
        = (Real.sqrt 2 / 6) * (ε / 2) * ((1 / (Q : ℝ)) * ∑ p ∈ S, |c p| / (p : ℝ)) := by ring
      _ ≤ 1 * (ε / 2) *
            (Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
              Real.sqrt ((Q : ℝ) + 8 * (P : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (by positivity)) habs
            (by positivity) (by positivity)
      _ = _ := by ring
  have htail :
      3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
          ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 ≤
        9 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := by
    have hc0 : 0 ≤ 3 / 4 * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => by positivity)
    calc 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3
        ≤ 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * (3 / (Q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hQ₂ Q hQ' N).1 hc0
      _ = _ := by ring
  linarith

/-- **Uniform Balanced-Regime Dual-Norm Law with Block-Mass Absorption and Tail Summation
(`exists_balanced_centredPrimeBlock_dualNorm_tail_summed_le`):**
For every aspect ratio `B ≥ 1` and `ε > 0`, there exists `P₀ : ℕ` such that for all `P ≥ P₀`,
`P ≤ Q ≤ B P`, `3 Q ≤ N`, and `S ⊆ (P, 2P]` of primes with `2P ≤ N`:
`∑ p ∈ S, |Λ_p(c'_Q)| / p ≤ ε √(∑ p²) √(Q + 8P²) Q^{-3/2} + 9/(4Q²) ∑ p² + 18/Q³ ∑ p³`. -/
theorem exists_balanced_centredPrimeBlock_dualNorm_tail_summed_le
    {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ {N P Q : ℕ} {S : Finset ℕ}, P₀ ≤ P → P ≤ Q → (Q : ℝ) ≤ B * P →
      3 * Q ≤ N → (∀ p ∈ S, p.Prime ∧ P < p ∧ p ≤ 2 * P ∧ p ≤ N) →
      ∑ p ∈ S, |kernelStatistic N (centredPrimeBlock Q) p| / p ≤
        ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
            (Real.sqrt ((Q : ℝ) + 8 * (P : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) +
          9 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2) +
          18 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3) := by
  obtain ⟨P₁, hP₁⟩ := exists_balanced_centredPrimeBlock_dualNorm_le hB (half_pos hε)
  obtain ⟨Q₂, hQ₂⟩ := eventually_atTop.mp
    eventually_sum_Icc_abs_centredPrimeBlock_div_cube_fourth_le
  refine ⟨max P₁ (max Q₂ 1), ?_⟩
  intro N P Q S hP hPQ hQB hN hS
  have hP' : P₁ ≤ P := (le_max_left _ _).trans hP
  have hQ1 : 1 ≤ Q := ((le_max_right _ _).trans ((le_max_right _ _).trans hP)).trans hPQ
  have hQ' : Q₂ ≤ Q := ((le_max_left _ _).trans ((le_max_right _ _).trans hP)).trans hPQ
  have h1 := hP₁ hP' hPQ hQB hN hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have habs := div_mul_sum_abs_div_prime_le_largeSieve hSp (fun _ => 1) hQ1
    (by positivity : (0 : ℝ) ≤ 8 * (P : ℝ) ^ 2)
  simp only [abs_one, one_pow, one_mul] at habs
  have hmass :
      (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * (ε / 2) / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ) ≤
        (ε / 2) * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
          (Real.sqrt ((Q : ℝ) + 8 * (P : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) := by
    have hcoeff : (1 / 6 + Real.pi ^ 2 / 72) * Real.sqrt 2 ≤ 1 := by
      linarith [one_div_six_add_pi_sq_div_72_mul_sqrt_two_le_half]
    calc (1 / 6 + Real.pi ^ 2 / 72) * (Real.sqrt 2 * (ε / 2) / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ)
        = ((1 / 6 + Real.pi ^ 2 / 72) * Real.sqrt 2) * (ε / 2) *
            ((1 / (Q : ℝ)) * ∑ p ∈ S, 1 / (p : ℝ)) := by ring
      _ ≤ 1 * (ε / 2) *
            (Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
              Real.sqrt ((Q : ℝ) + 8 * (P : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcoeff (by positivity)) habs
            (by positivity) (by positivity)
      _ = _ := by ring
  have htail3 :
      3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3 ≤
        9 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2) := by
    have hc0 : 0 ≤ 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => sq_nonneg _)
    calc 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 3
        ≤ 3 / 4 * (∑ p ∈ S, (p : ℝ) ^ 2) * (3 / (Q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hQ₂ Q hQ' N).1 hc0
      _ = _ := by ring
  have htail4 :
      6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4 ≤
        18 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3) := by
    have hc0 : 0 ≤ 6 * (∑ p ∈ S, (p : ℝ) ^ 3) :=
      mul_nonneg (by norm_num) (sum_nonneg fun _ _ => by positivity)
    calc 6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 4
        ≤ 6 * (∑ p ∈ S, (p : ℝ) ^ 3) * (3 / (Q : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left (hQ₂ Q hQ' N).2 hc0
      _ = _ := by ring
  linarith

/-- Whenever `(Q₀ : ℝ) ≤ δ ^ 2 * Q` (`0 ≤ δ`), the summed `1 / Q²` and `1 / Q³` prime-moment tails
are bounded by `δ` and `δ ^ 3` times the large-sieve factor. -/
theorem prime_moment_tails_le_largeSieve_of_le {Q Q₀ : ℕ} (hQ : 1 ≤ Q) {δ : ℝ} (hδ : 0 ≤ δ)
    (hQ₀Q : (Q₀ : ℝ) ≤ δ ^ 2 * Q) :
    Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 2 ≤
      δ * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) ∧
    (Q₀ : ℝ) * Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 3 ≤
      δ ^ 3 * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ₀0 : (0 : ℝ) ≤ Q₀ := Nat.cast_nonneg Q₀
  have hsqrtQ₀ : Real.sqrt (Q₀ : ℝ) ≤ δ * Real.sqrt (Q : ℝ) := by
    rw [← Real.sqrt_sq hδ, ← Real.sqrt_mul (sq_nonneg δ)]
    exact Real.sqrt_le_sqrt hQ₀Q
  have hcube : Real.sqrt ((Q₀ : ℝ) ^ 3) = (Q₀ : ℝ) * Real.sqrt (Q₀ : ℝ) := by
    rw [show (Q₀ : ℝ) ^ 3 = (Q₀ : ℝ) ^ 2 * Q₀ by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hQ₀0]
  have hQ₀_le_V : (Q₀ : ℝ) ≤ Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) := by
    calc (Q₀ : ℝ) = Real.sqrt ((Q₀ : ℝ) ^ 2) := (Real.sqrt_sq hQ₀0).symm
      _ ≤ Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith [sq_nonneg (Q₀ : ℝ)])
  have hR : Real.sqrt (Q : ℝ) / (Q : ℝ) ^ 2 = Real.sqrt (1 / (Q : ℝ) ^ 3) := by
    rw [show (Q : ℝ) ^ 2 = Real.sqrt ((Q : ℝ) ^ 4) by
      rw [show (Q : ℝ) ^ 4 = ((Q : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)],
      ← Real.sqrt_div hQ0.le]
    congr 1; field_simp
  have h1 : Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 2 ≤
      δ * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3) := by
    rw [hcube, show (Q₀ : ℝ) * Real.sqrt (Q₀ : ℝ) / (Q : ℝ) ^ 2 =
        (Q₀ : ℝ) * Real.sqrt (Q₀ : ℝ) * (1 / (Q : ℝ) ^ 2) by ring]
    calc (Q₀ : ℝ) * Real.sqrt (Q₀ : ℝ) * (1 / (Q : ℝ) ^ 2)
        ≤ Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * (δ * Real.sqrt (Q : ℝ)) *
            (1 / (Q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hQ₀_le_V hsqrtQ₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (by positivity)
      _ = δ * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * (Real.sqrt (Q : ℝ) / (Q : ℝ) ^ 2) := by
          ring
      _ = _ := by rw [hR]
  refine ⟨h1, ?_⟩
  rw [show (Q₀ : ℝ) * Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 3 =
      ((Q₀ : ℝ) / Q) * (Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 2) by ring]
  have hdiv : (Q₀ : ℝ) / Q ≤ δ ^ 2 := (div_le_iff₀ hQ0).mpr hQ₀Q
  calc ((Q₀ : ℝ) / Q) * (Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 2)
      ≤ δ ^ 2 * (δ * Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) :=
        mul_le_mul hdiv h1 (by positivity) (sq_nonneg δ)
    _ = _ := by ring

/-- **Single-Term Pure Large-Sieve Absorption for the Möbius Block
(`eventually_moebiusWindowRow_pure_largeSieve_le`):**
For every `ε > 0`, with `δ = min (ε / 14) 1`, eventually in `Q`, whenever `Q₀ ≤ δ² Q` and
`8 log₂ Q ≤ (ε/2)² p` on `S ⊆ [1, min(N, Q₀)]`, **every** remainder term (block mass, `n⁻³` tail,
and `n⁻⁴` tail) is absorbed into the single large-sieve bound:
- `|B(c, μ_Q) + m(c) R(μ_Q) + β(c) H(μ_Q)| ≤ ε √(∑ c(p)² p²) √(Q + 2Q₀²) Q^{-3/2}`, and
- `∑ p ∈ S, |Λ_p(μ_Q)| / p ≤ ε √(∑ p²) √(Q + 2Q₀²) Q^{-3/2}`. -/
theorem eventually_moebiusWindowRow_pure_largeSieve_le {ε : ℝ} (hε : 0 < ε) :
    let δ := min (ε / 14) 1
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ}, 2 ≤ Q₀ → (Q₀ : ℝ) ≤ δ ^ 2 * Q →
      Q + Q + Nat.log 2 Q ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (Nat.log 2 Q : ℝ) ≤ (ε / 4) ^ 2 * p) →
      (∀ c : ℕ → ℝ, (∀ n, c n ≠ 0 → n ∈ S) →
        |rowBilinear N c (moebiusWindowRow Q) +
            rowMean N c * vonMangoldtReadout N (moebiusWindowRow Q) +
            rowBeta N c * finiteHarmonicSum N (moebiusWindowRow Q)| ≤
          ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
            Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) ∧
      ∑ p ∈ S, |kernelStatistic N (moebiusWindowRow Q) p| / p ≤
        ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
          (Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) := by
  intro δ
  have hδ0 : 0 ≤ δ := le_min (by positivity) zero_le_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδ14 : δ ≤ ε / 14 := min_le_left _ _
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ]
  filter_upwards [eventually_abs_rowBilinear_moebiusWindowRow_tail_summed_le (half_pos hε),
    eventually_sum_abs_kernelStatistic_moebiusWindowRow_tail_summed_le (half_pos hε),
    eventually_ge_atTop 1] with Q hbil hdual hQ1
  intro N Q₀ S hQ₀ hQ₀Q hN hS hSP
  have hSN : ∀ p ∈ S, 1 ≤ p ∧ p ≤ N ∧ p ≤ Q₀ := fun p hp =>
    ⟨(hS p hp).1.one_lt.le, (hS p hp).2.1, (hS p hp).2.2⟩
  have hSQ : ∀ p ∈ S, 1 ≤ p ∧ p ≤ Q₀ := fun p hp => ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2⟩
  obtain ⟨ht1, ht2⟩ := prime_moment_tails_le_largeSieve_of_le hQ1 hδ0 hQ₀Q
  set V := Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)
  have hV0 : 0 ≤ V := by positivity
  constructor
  · intro c hsupp
    have hb := hbil hQ₀ hN hS (by rw [show ε / 2 / 2 = ε / 4 by ring]; exact hSP) hsupp
    have hcs := sum_Icc_abs_mul_sq_le_sqrt_sum_sq_mul_sq hSN hsupp
    set S₂ := Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2)
    have hS₂0 : 0 ≤ S₂ := Real.sqrt_nonneg _
    have hrem : 3 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 ≤
        (ε / 2) * S₂ * V := by
      calc 3 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2
          ≤ 3 / (4 * (Q : ℝ) ^ 2) * (Real.sqrt ((Q₀ : ℝ) ^ 3) * S₂) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
        _ = (3 / 4) * S₂ * (Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 2) := by ring
        _ ≤ (3 / 4) * S₂ * (δ * V) :=
            mul_le_mul_of_nonneg_left (by simpa [V, mul_assoc] using ht1) (by positivity)
        _ = (3 / 4 * δ) * S₂ * V := by ring
        _ ≤ (ε / 2) * S₂ * V :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hS₂0) hV0
    calc _ ≤ (ε / 2) * S₂ * V + 3 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := by
          simpa [V, mul_assoc] using hb
      _ ≤ (ε / 2) * S₂ * V + (ε / 2) * S₂ * V := add_le_add le_rfl hrem
      _ = _ := by simp only [V]; ring
  · have hd := hdual hQ₀ hN hS (by rw [show ε / 2 / 2 = ε / 4 by ring]; exact hSP)
    obtain ⟨hsq, hcube⟩ := sum_sq_and_cube_le_sqrt_sum_sq hSQ
    set S₂ := Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2)
    have hS₂0 : 0 ≤ S₂ := Real.sqrt_nonneg _
    have hrem1 : 3 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2) ≤ (3 / 4 * δ) * S₂ * V := by
      calc 3 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2)
          ≤ 3 / (4 * (Q : ℝ) ^ 2) * (Real.sqrt ((Q₀ : ℝ) ^ 3) * S₂) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (3 / 4) * S₂ * (Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 2) := by ring
        _ ≤ (3 / 4) * S₂ * (δ * V) :=
            mul_le_mul_of_nonneg_left (by simpa [V, mul_assoc] using ht1) (by positivity)
        _ = (3 / 4 * δ) * S₂ * V := by ring
    have hrem2 : 6 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3) ≤ (6 * δ) * S₂ * V := by
      calc 6 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3)
          ≤ 6 / (Q : ℝ) ^ 3 * ((Q₀ : ℝ) * Real.sqrt ((Q₀ : ℝ) ^ 3) * S₂) :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
        _ = 6 * S₂ * ((Q₀ : ℝ) * Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 3) := by ring
        _ ≤ 6 * S₂ * (δ ^ 3 * V) :=
            mul_le_mul_of_nonneg_left (by simpa [V, mul_assoc] using ht2) (by positivity)
        _ ≤ 6 * S₂ * (δ * V) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδ3 hV0) (by positivity)
        _ = (6 * δ) * S₂ * V := by ring
    have hsum_rem : (3 / 4 * δ + 6 * δ) * S₂ * V ≤ (ε / 2) * S₂ * V :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hS₂0) hV0
    linarith

/-- **Single-Term Pure Large-Sieve Absorption for the Centred Prime Block
(`eventually_centredPrimeBlock_pure_largeSieve_le`):**
For every `17/30 < α < 1` and `ε > 0`, with `δ = min (ε / 42) 1`, eventually in `Q`, whenever
`Q₀ ≤ δ² Q` and `8⌈(2Q)^α⌉(log 2Q + 1)² ≤ (ε/4)² p` on `S ⊆ [1, min(N, Q₀)]`, **every** remainder
term (block mass, `n⁻³` tail, and `n⁻⁴` tail) is absorbed into the single large-sieve bound:
- `|B(c, c'_Q) + m(c) R(c'_Q) + β(c) H(c'_Q)| ≤ ε √(∑ c(p)² p²) √(Q + 2Q₀²) Q^{-3/2}`, and
- `∑ p ∈ S, |Λ_p(c'_Q)| / p ≤ ε √(∑ p²) √(Q + 2Q₀²) Q^{-3/2}`. -/
theorem eventually_centredPrimeBlock_pure_largeSieve_le {α : ℝ}
    (hα : 17 / 30 < α) (hα1 : α < 1) {ε : ℝ} (hε : 0 < ε) :
    let δ := min (ε / 42) 1
    ∀ᶠ Q : ℕ in atTop, ∀ {N Q₀ : ℕ} {S : Finset ℕ}, 2 ≤ Q₀ → (Q₀ : ℝ) ≤ δ ^ 2 * Q →
      Q + Q + ⌈(2 * (Q : ℝ)) ^ α⌉₊ ≤ N + 1 → (∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) →
      (∀ p ∈ S, 8 * (⌈(2 * (Q : ℝ)) ^ α⌉₊ : ℝ) * (Real.log (2 * Q) + 1) ^ 2 ≤ (ε / 4) ^ 2 * p) →
      (∀ c : ℕ → ℝ, (∀ n, c n ≠ 0 → n ∈ S) →
        |rowBilinear N c (centredPrimeBlock Q) +
            rowMean N c * vonMangoldtReadout N (centredPrimeBlock Q) +
            rowBeta N c * finiteHarmonicSum N (centredPrimeBlock Q)| ≤
          ε * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
            Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) ∧
      ∑ p ∈ S, |kernelStatistic N (centredPrimeBlock Q) p| / p ≤
        ε * Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2) *
          (Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)) := by
  intro δ
  have hδ0 : 0 ≤ δ := le_min (by positivity) zero_le_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδ42 : δ ≤ ε / 42 := min_le_left _ _
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ]
  filter_upwards [eventually_abs_rowBilinear_centredPrimeBlock_tail_summed_le hα hα1 (half_pos hε),
    eventually_sum_abs_kernelStatistic_centredPrimeBlock_tail_summed_le hα hα1 (half_pos hε),
    eventually_ge_atTop 1] with Q hbil hdual hQ1
  intro N Q₀ S hQ₀ hQ₀Q hN hS hSP
  have hSN : ∀ p ∈ S, 1 ≤ p ∧ p ≤ N ∧ p ≤ Q₀ := fun p hp =>
    ⟨(hS p hp).1.one_lt.le, (hS p hp).2.1, (hS p hp).2.2⟩
  have hSQ : ∀ p ∈ S, 1 ≤ p ∧ p ≤ Q₀ := fun p hp => ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2⟩
  obtain ⟨ht1, ht2⟩ := prime_moment_tails_le_largeSieve_of_le hQ1 hδ0 hQ₀Q
  set V := Real.sqrt ((Q : ℝ) + 2 * (Q₀ : ℝ) ^ 2) * Real.sqrt (1 / (Q : ℝ) ^ 3)
  have hV0 : 0 ≤ V := by positivity
  constructor
  · intro c hsupp
    have hb := hbil hQ₀ hN hS (by rw [show ε / 2 / 2 = ε / 4 by ring]; exact hSP) hsupp
    have hcs := sum_Icc_abs_mul_sq_le_sqrt_sum_sq_mul_sq hSN hsupp
    set S₂ := Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2)
    have hS₂0 : 0 ≤ S₂ := Real.sqrt_nonneg _
    have hrem : 9 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 ≤
        (ε / 2) * S₂ * V := by
      calc 9 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2
          ≤ 9 / (4 * (Q : ℝ) ^ 2) * (Real.sqrt ((Q₀ : ℝ) ^ 3) * S₂) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
        _ = (9 / 4) * S₂ * (Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 2) := by ring
        _ ≤ (9 / 4) * S₂ * (δ * V) :=
            mul_le_mul_of_nonneg_left (by simpa [V, mul_assoc] using ht1) (by positivity)
        _ = (9 / 4 * δ) * S₂ * V := by ring
        _ ≤ (ε / 2) * S₂ * V :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hS₂0) hV0
    calc _ ≤ (ε / 2) * S₂ * V + 9 / (4 * (Q : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := by
          simpa [V, mul_assoc] using hb
      _ ≤ (ε / 2) * S₂ * V + (ε / 2) * S₂ * V := add_le_add le_rfl hrem
      _ = _ := by simp only [V]; ring
  · have hd := hdual hQ₀ hN hS (by rw [show ε / 2 / 2 = ε / 4 by ring]; exact hSP)
    obtain ⟨hsq, hcube⟩ := sum_sq_and_cube_le_sqrt_sum_sq hSQ
    set S₂ := Real.sqrt (∑ p ∈ S, (p : ℝ) ^ 2)
    have hS₂0 : 0 ≤ S₂ := Real.sqrt_nonneg _
    have hrem1 : 9 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2) ≤ (9 / 4 * δ) * S₂ * V := by
      calc 9 / (4 * (Q : ℝ) ^ 2) * (∑ p ∈ S, (p : ℝ) ^ 2)
          ≤ 9 / (4 * (Q : ℝ) ^ 2) * (Real.sqrt ((Q₀ : ℝ) ^ 3) * S₂) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (9 / 4) * S₂ * (Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 2) := by ring
        _ ≤ (9 / 4) * S₂ * (δ * V) :=
            mul_le_mul_of_nonneg_left (by simpa [V, mul_assoc] using ht1) (by positivity)
        _ = (9 / 4 * δ) * S₂ * V := by ring
    have hrem2 : 18 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3) ≤ (18 * δ) * S₂ * V := by
      calc 18 / (Q : ℝ) ^ 3 * (∑ p ∈ S, (p : ℝ) ^ 3)
          ≤ 18 / (Q : ℝ) ^ 3 * ((Q₀ : ℝ) * Real.sqrt ((Q₀ : ℝ) ^ 3) * S₂) :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
        _ = 18 * S₂ * ((Q₀ : ℝ) * Real.sqrt ((Q₀ : ℝ) ^ 3) / (Q : ℝ) ^ 3) := by ring
        _ ≤ 18 * S₂ * (δ ^ 3 * V) :=
            mul_le_mul_of_nonneg_left (by simpa [V, mul_assoc] using ht2) (by positivity)
        _ ≤ 18 * S₂ * (δ * V) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδ3 hV0) (by positivity)
        _ = (18 * δ) * S₂ * V := by ring
    have hsum_rem : (9 / 4 * δ + 18 * δ) * S₂ * V ≤ (ε / 2) * S₂ * V :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hS₂0) hV0
    linarith

/-! ## §4. Equivalence of Quantitative Short-Window Power Savings with the Complete Coupled Receiver -/

/-- **Complete Equivalence of Prime Short-Window Power Savings with Sub-Half-Damping Receiver
Admission (`primePowerWindowSaving_iff_all_receiver_forms`):**
Upgrading the qualitative `o(1)` short-window mean-square saving of the centred prime block to a
power saving at some window exponent `α ∈ (0, 1)` (`PrimePowerWindowSaving`) is equivalent to:
1. the quasi-Riemann hypothesis `zetaZeroAbscissa < 1`,
2. `receiverDampingRate < 1 / 2`,
3. admission of a fixed-width sub-half-damping band `Set.Ioo ε₀ (1 / 2) ⊆ receiverDampings`, and
4. admission of a fixed-width sub-half-damping band `Set.Ioo ε₀ (1 / 2) ⊆ interiorReceiverDampings`. -/
theorem primePowerWindowSaving_iff_all_receiver_forms :
    (PrimePowerWindowSaving ↔ zetaZeroAbscissa < 1) ∧
    (PrimePowerWindowSaving ↔ receiverDampingRate < 1 / 2) ∧
    (PrimePowerWindowSaving ↔ ∃ ε₀ : ℝ, ε₀ < 1 / 2 ∧ Set.Ioo ε₀ (1 / 2) ⊆ receiverDampings) ∧
    (PrimePowerWindowSaving ↔ ∃ ε₀ : ℝ, ε₀ < 1 / 2 ∧ Set.Ioo ε₀ (1 / 2) ⊆ interiorReceiverDampings) := by
  have h1 := primePowerWindowSaving_iff
  have h2 := primePowerWindowSaving_iff_receiverDampingRate_lt_half
  have h3 : (∃ ε₀ : ℝ, ε₀ < 1 / 2 ∧ Set.Ioo ε₀ (1 / 2) ⊆ receiverDampings) ↔
      receiverDampingRate < 1 / 2 := by
    constructor
    · rintro ⟨ε₀, hε₀, hsub⟩
      have hacc : ε₀ ∈ derivedSet receiverDampings :=
        mem_derivedSet.mpr (accPt_of_Ioo_subset hε₀ hsub)
      exact lt_of_le_of_lt (csInf_le bddBelow_derivedSet_receiverDampings hacc) hε₀
    · intro hlt
      refine ⟨zetaZeroAbscissa - 1 / 2, ?_, fun ε hε =>
        Ioi_zetaZeroAbscissa_sub_half_subset_receiverDampings hε.1⟩
      linarith [zetaZeroAbscissa_le_half_add_receiverDampingRate]
  have h4 : (∃ ε₀ : ℝ, ε₀ < 1 / 2 ∧ Set.Ioo ε₀ (1 / 2) ⊆ receiverDampings) ↔
      (∃ ε₀ : ℝ, ε₀ < 1 / 2 ∧ Set.Ioo ε₀ (1 / 2) ⊆ interiorReceiverDampings) := by
    rw [interiorReceiverDampings_eq_receiverDampings]
  exact ⟨h1, h2, h2.trans h3.symm, (h2.trans h3.symm).trans h4⟩

/-- **Complete Equivalence of Möbius Short-Window Power Savings with Sub-Half-Damping Receiver
Admission (`moebiusPowerWindowSaving_iff_all_receiver_forms`):**
Upgrading the qualitative `o(1)` short-window mean-square saving of the Möbius block to a power
saving at some window exponent `α ∈ (0, 1)` (`MoebiusPowerWindowSaving`) is equivalent to:
1. the quasi-Riemann hypothesis `zetaZeroAbscissa < 1`,
2. `receiverDampingRate < 1 / 2`,
3. admission of a fixed-width sub-half-damping band `Set.Ioo ε₀ (1 / 2) ⊆ receiverDampings`, and
4. admission of a fixed-width sub-half-damping band `Set.Ioo ε₀ (1 / 2) ⊆ interiorReceiverDampings`. -/
theorem moebiusPowerWindowSaving_iff_all_receiver_forms :
    (MoebiusPowerWindowSaving ↔ zetaZeroAbscissa < 1) ∧
    (MoebiusPowerWindowSaving ↔ receiverDampingRate < 1 / 2) ∧
    (MoebiusPowerWindowSaving ↔ ∃ ε₀ : ℝ, ε₀ < 1 / 2 ∧ Set.Ioo ε₀ (1 / 2) ⊆ receiverDampings) ∧
    (MoebiusPowerWindowSaving ↔ ∃ ε₀ : ℝ, ε₀ < 1 / 2 ∧ Set.Ioo ε₀ (1 / 2) ⊆ interiorReceiverDampings) := by
  obtain ⟨h1, h2, h3, h4⟩ := primePowerWindowSaving_iff_all_receiver_forms
  have heq := primePowerWindowSaving_iff_moebiusPowerWindowSaving.symm
  exact ⟨heq.trans h1, heq.trans h2, heq.trans h3, heq.trans h4⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
